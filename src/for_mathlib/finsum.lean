import data.finsupp 
import data.support
import data.setoid.partition

noncomputable theory

open_locale classical big_operators

noncomputable def finsum {ι M} [add_comm_monoid M] (f : ι → M) : M :=
if h : (function.support f).finite then ∑ x in h.to_finset, f x else 0

section finsum2

-- we might not need this section

noncomputable def finsum2 {ι M} [add_comm_monoid M] (f : ι → M) : M :=
if h : ∃ f' : ι →₀ M, f = f' then (classical.some h).sum (λ _ a, a) else 0

theorem finsum_eq_finsum2 {ι M} [add_comm_monoid M] (f : ι → M) : finsum f = finsum2 f :=
begin
  unfold finsum,
  unfold finsum2,
  symmetry,
  split_ifs with h1 h2 h3,
  { unfold finsupp.sum,
    congr',
    { ext x,
      rw finsupp.mem_support_iff,
      rw (classical.some_spec h1).symm,
      rw set.finite.mem_to_finset,
      refl },
    { exact (classical.some_spec h1).symm } },
  { exfalso,
    apply h2,
    clear h2,
    rcases h1 with ⟨h1, rfl⟩,
    exact h1.finite_supp },
  { exfalso,
    apply h1,
    clear h1,
    let f' : ι →₀ M := 
    { support := h3.to_finset,
      to_fun := f,
      mem_support_to_fun := begin
        intro i,
        simp only [function.mem_support, set.finite.mem_to_finset],
      end },
    use f',
    refl },
  { refl }
end .

end finsum2

noncomputable def finsum_in {ι M} [add_comm_monoid M] (s : set ι) (f : ι → M) : M :=
finsum (λ i, if i ∈ s then f i else 0)

notation `∑' ` binders ` in ` s `, ` r:(scoped:67 f, finsum_in s f) := r
notation `∑' ` binders `, ` r:(scoped:67 f, finsum f) := r

-- lemma is_finite_supp {M β} [has_zero β] (f : M →₀ β) : is_finite {a // f a ≠ 0} :=
-- f.finite_supp

universes u v

variables {ι : Type u} {M : Type v} [add_comm_monoid M]
variables {f : ι → M}

def finset.univ' (ι : Type*) : finset ι := if h : nonempty (fintype ι) then
  (classical.choice h).elems else ∅

open finset finsupp

lemma univ'_eq_univ_of_fintype [h : fintype ι] : univ' ι = univ :=
begin
  unfold univ', unfold univ,
  convert dif_pos (nonempty.intro h)
end

lemma mem_univ' [fintype ι] (x : ι) : x ∈ univ' ι :=
begin
  rw univ'_eq_univ_of_fintype, 
  exact mem_univ _
end

noncomputable def to_finsupp (f : ι → M) : ι →₀ M := 
{ support := filter (λ x, f x ≠ 0) $ univ' ι,
  to_fun := λ x, if h : x ∈ univ' ι then f x else 0,
  mem_support_to_fun := begin
    intros,
    split_ifs,
    { simp only [*, true_and, mem_filter]},
    { simp only [*, mem_filter, eq_self_iff_true, not_true, ne.def, false_and]}  
  end }

@[simp] lemma eq_finsupp [fintype ι] (f : ι → M) : 
  (to_finsupp f : ι → M) = f :=
funext (λ x, dif_pos (mem_univ' x))

-- lemma finsum_def_of_finite (f : ι → M) : 
--   finsum f = (finsupp_of_is_finite f).sum (λ _ a, a) := 
-- begin
--   unfold finsum,
--   have h : ∃ (f' : ι →₀ M), f = f' := ⟨finsupp_of_is_finite f, rfl⟩,
--   rw dif_pos h,
--   congr, ext, rw finsupp_of_is_finite_eq,
--   solve_by_elim [(classical.some_spec h).symm],
-- end

-- (on_finset s f hf).sum g = ∑ a in s, g a (f a) :=

lemma finsum_in_eq_finset_sum (f : ι → M) (s : finset ι) :
  ∑' x in ↑s, f x = s.sum f :=
begin
  unfold finsum_in, unfold finsum,
  rw dif_pos,
  { rw [finset.sum_ite, sum_const_zero, add_zero],
    refine finset.sum_subset _ _,
    { apply set.finite.subset (s.finite_to_set),
      rintro x h,
      rw function.mem_support at h,
      split_ifs at h, assumption, contradiction },
    { intro _, simp only [and_imp, mem_filter, imp_self, mem_coe, forall_true_iff] },
    { simp only [function.mem_support, mem_filter, and_true, if_true, 
        set.finite.mem_to_finset, mem_coe, eq_self_iff_true,
        classical.not_not, forall_true_iff] { contextual := tt } } },
end

lemma finsum_in_eq_finsum (f : ι → M) (s : set ι) :
  ∑' x in s, f x = ∑' x : s, f x :=
begin
  unfold finsum_in,
  unfold finsum,
  split_ifs,
  { rw [sum_ite, sum_const_zero, add_zero],
    convert (sum_subtype_eq_sum_filter f).symm,
    ext x,
    cases x with x hx,
    simp [function.support]; split_ifs, refl },
  { exfalso,
    apply h_1, clear h_1,
    apply set.finite_of_finite_image (_ : set.inj_on (subtype.val : s → ι) _) _,
    { apply function.injective.inj_on, exact subtype.val_injective },
    apply set.finite.subset h,
    rintro _ ⟨⟨a, ha⟩, hf, rfl⟩,
    rw function.mem_support at hf ⊢,
    rw if_pos ha,
    exact hf },
  { exfalso,
    apply h, clear h,
    convert set.finite.image (λ (x : s), x.1) h_1,
    ext x,
    rw function.mem_support,
    split,
    { intro h,
      split_ifs at h,
      { use ⟨x, h_2⟩,
        rw function.mem_support,
        use h },
      { contradiction } },
    { rintro ⟨i, hi, rfl⟩,
      rw if_pos i.2,
      exact hi } },
  { refl }
end

/- lemma finite_support_of_fintype [fintype ι] (f : ι → M) : 
(function.support f).finite := set.finite.of_fintype (function.support f) -/

lemma finsum_in_def_of_finite' {f : ι → M} (s : set ι) 
  (hf : (function.support f).finite) : 
  ∑' x in s, f x = (filter (∈ s) hf.to_finset).sum f := 
begin
  unfold finsum_in, unfold finsum,
  rw dif_pos,
    { rw [sum_ite, sum_const_zero, add_zero],
      refine finset.sum_subset _ _,
        { refine set.finite.subset hf (λ x hx, _),
          rw function.mem_support at ⊢ hx,
          intro h, apply hx,
          split_ifs, exact h, refl },
        { intros x hx,
          rw mem_filter at ⊢ hx,
          cases hx with hx₀ hx₁,
          refine ⟨_, hx₁⟩,
          rw [set.finite.mem_to_finset, function.mem_support, if_pos hx₁] at hx₀,
          rw set.finite.mem_to_finset, exact hx₀ },
    { simp [function.mem_support] {contextual := tt} } }
end .

-- ↓ Rewrite below as a corollary of `finsum_in_def_of_finite'`
lemma finsum_in_def_of_finite [fintype ι] (f : ι → M) (s : set ι) : 
  ∑' x in s, f x = s.to_finset.sum f := 
begin
  unfold finsum_in,
  unfold finsum,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  rw [finset.sum_ite, sum_const_zero, add_zero],
  refine finset.sum_subset _ _,
  { intro x, simp only [and_imp, mem_filter, 
                        imp_self, set.mem_to_finset, forall_true_iff]},
  { simp only [function.mem_support, mem_filter, and_true, if_true, 
               set.finite.mem_to_finset, set.mem_to_finset, eq_self_iff_true,
 classical.not_not, forall_true_iff] {contextual := tt} }
end

lemma finsum_in_def_of_finite''' (f : ι → M) {s : set ι} (h : s.finite) : 
  ∑' x in s, f x = h.to_finset.sum f := 
begin
  rw ←finsum_in_eq_finset_sum f,
  congr, simp,    
end

lemma finsum_def_of_finite [h : fintype ι] (f : ι → M) : 
  ∑' x : ι, f x = (finset.univ' ι).sum f :=
begin
  unfold finsum,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  refine finset.sum_subset (λ _ _, mem_univ' _) _,
    intros _ _ hx, 
    rw ←function.nmem_support,
    simpa using hx,
end

lemma finsum_def_of_finite' {f : ι → M} (hf : (function.support f).finite) : 
  ∑' x : ι, f x = hf.to_finset.sum f :=
begin
  unfold finsum,
  rw dif_pos hf
end

lemma finsum_def_of_infinite {f : ι → M} (hf : ¬(function.support f).finite) : 
  ∑' x : ι, f x = 0 :=
begin
  unfold finsum,
  rw dif_neg hf
end

lemma finsum_eq_finsum_in_univ (f : ι → M) : 
  ∑' x : ι, f x = ∑' x in set.univ, f x :=
begin
  by_cases ((function.support f).finite),
    { rw [finsum_def_of_finite' h, finsum_in_def_of_finite' _ h], simp },
    { unfold finsum_in,
      rw [finsum_def_of_infinite h, finsum_def_of_infinite], simpa }
end

lemma finsum_ext {s t : set ι} {f₁ f₂ : ι → M} (h₀ : s = t) 
  (h₁ : ∀ x ∈ t, f₁ x = f₂ x) : ∑' x in s, f₁ x = ∑' x in t, f₂ x :=
begin
  subst h₀,
  unfold finsum_in,
  congr',
  ext x,
  split_ifs,
  { exact h₁ x h },
  { refl },
end

lemma finsum_union [fintype ι] {s t : set ι} {f : ι → M} (h : disjoint s t) : 
  ∑' x in (s ∪ t), f x = ∑' x in s, f x + ∑' x in t, f x :=
begin
  iterate 3 { rw finsum_in_def_of_finite },
  rw ←finset.sum_union, congr', 
    { ext, simp }, 
    { intros a ha,
      apply @h a,
      simpa using ha }
end

lemma finsum_bind {γ} [fintype γ] [fintype ι] {s : set γ} {t : γ → set ι} 
  (f : ι → M) (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) : 
  (∑' x in (⋃ x ∈ s, t x), f x) = ∑' x in s, ∑' i in t x, f i :=
begin
  iterate 2 { rw finsum_in_def_of_finite },
  conv_rhs { congr, skip, funext, rw finsum_in_def_of_finite },
    { convert @sum_bind _ _ _ f _ _ s.to_finset (λ x, (t x).to_finset) 
      (begin
        intros x hx y hy hxy a ha,
        specialize h x (set.mem_to_finset.1 hx) y (set.mem_to_finset.1 hy) hxy,
        apply @h a, simpa using ha end),
      { ext, rw [mem_bind, set.mem_to_finset, set.mem_bUnion_iff],
        split; intro ha; rcases ha with ⟨x, hx₀, hx₁⟩,
          exact ⟨x, set.mem_to_finset.2 hx₀, set.mem_to_finset.2 hx₁⟩,
          exact ⟨x, set.mem_to_finset.1 hx₀, set.mem_to_finset.1 hx₁⟩ } },
end

-- def fincard (X : Type*) : ℕ :=
-- if h : nonempty (fintype X) then @fintype.card X (classical.choice h) else 0 

def fincard' (X : Type u) : ℕ := finset.card $ finset.univ' X

namespace fincard

lemma eq_finset_card (X : Type u) [fintype X] : 
  fincard' X = finset.card (univ : finset X) :=
begin
  unfold fincard',
  congr',
  unfold univ',
  rw dif_pos,
  { congr' },
  { apply nonempty.intro,
    assumption },
end

lemma eq_finset_card' {X : Type u} [fintype X] (s : set X) : 
  fincard' s = s.to_finset.card :=
by rw [eq_finset_card, set.to_finset_card]; refl

theorem card_eq_fincard (X : Type*) [h : fintype X] : fintype.card X = fincard' X :=
begin
  simp only [fincard', univ', nonempty.intro h, dif_pos],
  congr,
end

theorem fincard_eq_zero {X : Type*} (h : ¬nonempty (fintype X)) : fincard' X = 0 :=
congr_arg finset.card (dif_neg h)

@[simp] lemma empty : fincard' empty = 0 :=
begin
  rw ←card_eq_fincard,
  simp,
end

lemma of_equiv {X Y : Type*} (h : X ≃ Y) : fincard' X = fincard' Y :=
begin
  by_cases h2 : nonempty (fintype X),
  { cases h2,
    resetI,
    letI : fintype Y := fintype.of_equiv X h,
    rw [←card_eq_fincard X, ←card_eq_fincard Y, fintype.of_equiv_card] },
  { have h3 : ¬nonempty (fintype Y),
    { rintros ⟨_⟩,
      exactI h2 ⟨fintype.of_equiv _ h.symm⟩ },
    simp [fincard_eq_zero, *] }
end

theorem of_empty {X : Type*} (hX : X → false) : fincard' X = 0 :=
by simp [fincard.of_equiv (equiv.equiv_empty hX)]

theorem card_eq_zero_iff {X : Type*} [fintype X] (s : set X) : 
  fincard' s = 0 ↔ s = ∅ := 
begin
  rw [eq_finset_card', finset.card_eq_zero, ←set.to_finset_empty],
  apply set.to_finset_inj
end

lemma card_eq_sum_one_of_fintype {X : Type u} [h : fintype X] : 
  fincard' X = ∑' x : X, 1 :=
begin
  rw [eq_finset_card, finset.card_univ, finsum_def_of_finite],
  unfold univ',
  rw dif_pos (nonempty.intro h),
  simp only [mul_one, nat.cast_id, nsmul_eq_mul, sum_const],
  congr'
end

lemma card_eq_sum_one_of_nfintype {X : Type u} (h : ¬ nonempty (fintype X)) : 
  fincard' X = ∑' x : X, 1 :=
begin
  unfold finsum,
  rw dif_neg, exact fincard_eq_zero h,
  suffices : function.support (λ (x : X), 1) = set.univ,
    rw this, intro h',
    exact h (nonempty.intro 
      ⟨h'.to_finset, λ x, set.finite.mem_to_finset.2 (set.mem_univ _)⟩),
  rw set.eq_univ_iff_forall,
  intro x, rw function.mem_support, norm_num,
end

lemma card_eq_sum_one {X : Type u} : fincard' X = ∑' x : X, 1 :=
begin
  by_cases (nonempty (fintype X)),
    { haveI := classical.choice h,
      exact card_eq_sum_one_of_fintype },
    { exact card_eq_sum_one_of_nfintype h }
end

lemma eq_finset_card'' {X : Type u} {s : set X} (h : s.finite) : 
  fincard' s = h.to_finset.card := 
begin
  rw [card_eq_sum_one, ←finsum_in_eq_finsum (λ _, 1), 
      finsum_in_def_of_finite''', finset.card_eq_sum_ones],
end

end fincard

lemma fintype.of_finite_support {X : Type u} 
  (h : (function.support (λ _ : X, 1)).finite) : 
  nonempty $ fintype X := 
begin
  unfold function.support at h,
  replace h : (@set.univ X).finite, simpa using h,
  exact nonempty.intro 
    (@fintype.of_equiv X (set.univ) (classical.choice h) (equiv.set.univ X))
end

namespace fincard

lemma card_eq_zero_of_infinite {X : Type u} {s : set X} (h : ¬ s.finite) : 
  fincard' s = 0 := 
begin
  rw card_eq_sum_one,
  exact finsum_def_of_infinite (λ h', h $ fintype.of_finite_support h')
end

@[simp] theorem card_singleton_eq_one {X : Type*} {x : X} : 
  fincard' ({x} : set X) = 1 :=
begin
  rw [eq_finset_card'' (set.finite_singleton x), set.finite.to_finset, finset.card_eq_one],
  refine ⟨x, _⟩, ext; simp
end

theorem card_eq_one_iff_singleton {X : Type*} {s : set X} : 
  fincard' s = 1 ↔ ∃ x : X, s = {x} :=
begin
  split,
    { by_cases h : s.finite,
        { rw [eq_finset_card'' h, finset.card_eq_one],
          rintro ⟨x, hx⟩,
          refine ⟨x, _⟩,
          rw ←@set.finite.coe_to_finset _ s h, simp [hx] },
        { finish [card_eq_zero_of_infinite h] } },
    { rintro ⟨_, rfl⟩,
      exact card_singleton_eq_one }
end

end fincard 

-- Is this really not in the library?
lemma set.eq_singleton_iff_unique_mem {X : Type*} {x : X} {s : set X} : 
  s = {x} ↔ x ∈ s ∧ ∀ y ∈ s, x = y :=
begin
  split,
    { rintro rfl, simp },
    { rintro ⟨h₀, h₁⟩,
      ext, split; finish }
end

namespace fincard

theorem card_eq_one_iff_unique_mem {X : Type*} {s : set X} : 
  fincard' s = 1 ↔ ∃! x : X, x ∈ s :=
begin
  rw card_eq_one_iff_singleton, 
  unfold exists_unique,
  split,
    rintro ⟨_, _⟩, finish,
    rintro ⟨x, _, _⟩, refine ⟨x, _⟩, 
    finish [set.eq_singleton_iff_unique_mem],
end

private theorem prod_of_empty_left {X : Type*} (h : X → false) (Y : Type*) :
  fincard' (X × Y) = fincard' X * fincard' Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.fst), zero_mul]

private theorem prod_of_empty_right (X : Type*) {Y : Type*} (h : Y → false) :
  fincard' (X × Y) = fincard' X * fincard' Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.snd), mul_zero]

private theorem prod_of_finite {X Y : Type*}
  (hX : nonempty (fintype X)) (hY : nonempty (fintype Y)) :
fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  unfreezingI {cases hX with hX, cases hY with hY},
  -- change this to squeeze_simp and watch Lean time out
  simp [←card_eq_fincard],
end

private theorem prod_of_infinite_left {X Y : Type*}
  (hX : ¬nonempty (fintype X)) (hY : nonempty Y) :
fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  have h : ¬nonempty (fintype (X × Y)),
  { rw not_nonempty_fintype at ⊢ hX,
    unfreezingI {cases hY with y},
    apply infinite.of_injective (λ x, (x, y) : X → X × Y),
    rintros _ _ ⟨_, _⟩, refl
  },
  simp [fincard_eq_zero, *],
end

private theorem prod_of_infinite_right {X Y : Type*}
  (hX : nonempty X) (hY : ¬nonempty (fintype Y)) : 
fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  have h : ¬nonempty (fintype (X × Y)),
  { rw not_nonempty_fintype at ⊢ hY,
    unfreezingI {cases hX with x},
    apply infinite.of_injective (prod.mk x : Y → X × Y),
    rintros _ _ ⟨_, _⟩, refl
  },
  simp [fincard_eq_zero, *],
end

theorem prod (X Y : Sort*) : fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  by_cases hX : X → false,
  { exact prod_of_empty_left hX _},
  rw [←not_nonempty_iff_imp_false, not_not] at hX,
  by_cases hY : Y → false,
  { exact prod_of_empty_right _ hY},
  rw [←not_nonempty_iff_imp_false, not_not] at hY,
  by_cases hX2 : nonempty (fintype X),
  { by_cases hY2 : nonempty (fintype Y),
    { exact prod_of_finite hX2 hY2},
    { exact prod_of_infinite_right hX hY2},
  },
  { exact prod_of_infinite_left hX2 hY}
end

end fincard 

lemma finsum_const {X Y : Type} [fintype X] [add_comm_monoid Y] 
  (s : set X) (m : Y) : ∑' x in s, m = fincard' s •ℕ m := 
by rw [finsum_in_def_of_finite, finset.sum_const m, ←fincard.eq_finset_card' s]

lemma finsum_const_nat {X : Type} [fintype X] {s : set X} {m : ℕ} {f : X → ℕ} 
  (h : ∀ x ∈ s, f x = m) : ∑' x in s, f x = fincard' s * m :=
begin
  rw [←nat.nsmul_eq_mul, ←(finsum_const s m)],
  exact finsum_ext rfl h
end

namespace fincard

theorem card_eq_finsum_partition {X : Type} [h : fintype X] {s : set (set X)} 
  (hS : setoid.is_partition s) : fincard' X = ∑' x in s, fincard' x := 
begin
  conv_rhs { congr, skip, funext, rw card_eq_sum_one },
  simp_rw ←finsum_in_eq_finsum (λ _, 1),
  rw [←finsum_bind _, card_eq_sum_one, finsum_def_of_finite, finsum_in_def_of_finite],
    { congr, unfold univ',
      rw [dif_pos (nonempty.intro h), ←set.sUnion_eq_bUnion, 
        setoid.is_partition.sUnion_eq_univ hS],
      ext, simp [fintype.complete] },
    { exact hS.pairwise_disjoint },
    all_goals { apply_instance }
end

lemma preimage_is_partition {X Y : Type} [fintype X] (f : X → Y) :
  setoid.is_partition $ (λ y, f⁻¹' {y}) '' (set.range f) :=
begin
  split,
  { intro h,
    rw set.mem_image at h,
    rcases h with ⟨y, ⟨x, rfl⟩, hy⟩,
    apply set.not_mem_empty x,
    rw ←hy,
    simp },
  { intro x,
    use f⁻¹' {f x},
    split,
    { suffices : ∃ (a : X), f ⁻¹' {f a} = f ⁻¹' {f x},
        simpa,
      use x
    },
    { 
      rintro _ ⟨⟨t, h1, rfl⟩, h2, h3⟩,
      change f x = t at h2,
      subst h2 } }
end

lemma finset.ne_empty_iff_exists_mem {M : Type u} {s : finset M} : s ≠ ∅ ↔ ∃ x : M, x ∈ s :=
begin
  rw ←nonempty_iff_ne_empty,
  refl
end

lemma finsum_fibres {X Y : Type} [fintype X] (f : X → Y) :
  ∑' y : Y, fincard' (f⁻¹' {y}) = fincard' X :=
begin
  simp_rw eq_finset_card',
  unfold fincard',
  rw univ'_eq_univ_of_fintype,
  rw finset.card_eq_sum_ones,
  rw sum_comp (λ y, 1) f,
  simp,
  unfold finsum,
  split_ifs,
  { congr',
    ext x,
    rw set.finite.mem_to_finset,
    rw function.mem_support,
    split,
    { rintro h,
      have h2 : (filter (λ (x_1 : X), f x_1 = x) univ) ≠ ∅,
      { intro h3,
        apply h,
        rwa card_eq_zero,
      },
      rw ←nonempty_iff_ne_empty at h2,
      cases h2 with a ha,
      rw mem_image,
      use a,
      use mem_univ a,
      simpa using ha },
    { rw mem_image,
      rintro ⟨a, ha, rfl⟩,
      apply card_ne_zero_of_mem,
      simp },
  },
  { exfalso,
    apply h, clear h,
    convert set.finite.image f set.finite_univ,
    ext x,
    rw function.mem_support,
    rw ←nat.pos_iff_ne_zero,
    rw card_pos,
    split,
    { rintro ⟨a, ha⟩,
      use a,
      use set.mem_univ a,
      simpa using ha },
    { rintro ⟨a, _, rfl⟩,
      use a,
      simp } },
end

lemma card_classes (S : Type) [fintype S] {h : setoid S} :
  fincard' S = ∑' i : quotient h, fincard' ((quotient.mk : S → quotient h) ⁻¹' {i}) :=
(finsum_fibres (quotient.mk : S → quotient h)).symm

lemma finsum_in_filter [fintype ι] (s : set ι) (p : ι → Prop) (f : ι → M) :
  ∑' i in {i ∈ s | p i}, f i + ∑' i in {i ∈ s | ¬ p i}, f i = ∑' i in s, f i :=
begin
  -- change to finset.sum then use corresponding lemma
  convert (finsum_union (_ : (disjoint {i ∈ s | p i} _))).symm,
  { ext x; by_cases p x; finish }, -- case split shouldn't be needed I guess
  { intro x, finish }
end

lemma finsum_nsmul [fintype ι] (s : set ι) (n : ℕ) (f : ι → M) :
  (∑' x in s, n •ℕ (f x)) = n •ℕ ((∑' x in s, f x)) :=
begin
  iterate 2 { rw finsum_in_def_of_finite },
  exact finset.sum_nsmul _ _ _
end

lemma finsum_divisible_by [fintype ι] (s : set ι) (k : ℕ) (f : ι → ℕ) 
  (hf : ∀ x ∈ s, k ∣ f x) : k ∣ ∑' x in s, f x :=
begin
  rw finsum_in_def_of_finite,
  apply dvd_sum, simpa,
end

end fincard


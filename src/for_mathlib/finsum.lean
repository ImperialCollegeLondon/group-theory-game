import data.finsupp 
import data.support
import data.setoid.partition

noncomputable theory

open_locale classical big_operators


noncomputable def finsum {ι α} [add_comm_monoid α] (f : ι → α) : α :=
if h : (function.support f).finite then ∑ x in h.to_finset, f x else 0

section finsum2

-- we might not need this section

noncomputable def finsum2 {ι α} [add_comm_monoid α] (f : ι → α) : α :=
if h : ∃ f' : ι →₀ α, f = f' then (classical.some h).sum (λ _ a, a) else 0

theorem finsum_eq_finsum2 {ι α} [add_comm_monoid α] (f : ι → α) : finsum f = finsum2 f :=
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
    let f' : ι →₀ α := 
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

noncomputable def finsum_in {ι α} [add_comm_monoid α] (s : set ι) (f : ι → α) : α :=
finsum (λ i, if i ∈ s then f i else 0)

notation `∑ ` binder ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r
notation `∑ ` binder `, ` r:(scoped:67 f, finsum f) := r

-- lemma is_finite_supp {α β} [has_zero β] (f : α →₀ β) : is_finite {a // f a ≠ 0} :=
-- f.finite_supp

universes u v

variables {ι : Type u} {α : Type v} [add_comm_monoid α]
variables {f : ι → α}

def finset.univ' (ι : Type*) : finset ι := if h : nonempty (fintype ι) then
  (classical.choice h).elems else ∅

open finset finsupp

lemma mem_univ' {ι : Type u} [fintype ι] (x : ι) : x ∈ univ' ι :=
begin
  unfold univ',
  rw dif_pos (nonempty.intro _inst_2),
  convert fintype.complete x,
end

noncomputable def to_finsupp (f : ι → α) : ι →₀ α := 
{ support := filter (λ x, f x ≠ 0) $ univ' ι,
  to_fun := λ x, if h : x ∈ univ' ι then f x else 0,
  mem_support_to_fun := begin
    intros,
    split_ifs,
    { simp only [*, true_and, mem_filter]},
    { simp only [*, mem_filter, eq_self_iff_true, not_true, ne.def, false_and]}  
  end }

@[simp] lemma eq_finsupp [fintype ι] (f : ι → α) : 
  (to_finsupp f : ι → α) = f :=
funext (λ x, dif_pos (mem_univ' x))

-- lemma finsum_def_of_finite (f : ι → α) : 
--   finsum f = (finsupp_of_is_finite f).sum (λ _ a, a) := 
-- begin
--   unfold finsum,
--   have h : ∃ (f' : ι →₀ α), f = f' := ⟨finsupp_of_is_finite f, rfl⟩,
--   rw dif_pos h,
--   congr, ext, rw finsupp_of_is_finite_eq,
--   solve_by_elim [(classical.some_spec h).symm],
-- end

-- (on_finset s f hf).sum g = ∑ a in s, g a (f a) :=

lemma finsum_in_eq_finset_sum (f : ι → α) (s : finset ι) :
∑ x ∈ ↑s, f x = s.sum f :=
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

lemma finsum_in_eq_finsum (f : ι → α) (s : set ι) :
  ∑ x ∈ s, f x = ∑ x : s, f x :=
begin
  unfold finsum_in,
  unfold finsum,
  split_ifs,
  rw sum_ite,
  sorry,sorry,sorry,sorry,
end

lemma finsum_in_def_of_finite [fintype ι] (f : ι → α) (s : set ι) : 
  ∑ x ∈ s, f x = s.to_finset.sum f := 
begin
  unfold finsum_in,
  unfold finsum,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  rw [finset.sum_ite, sum_const_zero, add_zero],
  refine finset.sum_subset _ _,
  { intro x, simp only [and_imp, mem_filter, imp_self, set.mem_to_finset, forall_true_iff]},
  { simp only [function.mem_support, mem_filter, and_true, if_true, set.finite.mem_to_finset, set.mem_to_finset, eq_self_iff_true,
 classical.not_not, forall_true_iff] {contextual := tt} }
end

lemma finsum_def_of_finite [h : fintype ι] (f : ι → α) : 
  ∑ x : ι, f x = (finset.univ' ι).sum f :=
begin
  unfold finsum,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  refine finset.sum_subset (λ _ _, mem_univ' _) _,
    intros _ _ hx, 
    rw ←function.nmem_support,
    simpa using hx,
end

lemma finsum_ext {s t : set ι} {f₁ f₂ : ι → α} (h₀ : s = t) 
  (h₁ : ∀ x ∈ t, f₁ x = f₂ x) : ∑ x ∈ s, f₁ x = ∑ x ∈ t, f₂ x :=
begin
  subst h₀,
  unfold finsum_in,
  congr',
  ext x,
  split_ifs,
  { exact h₁ x h },
  { refl },
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

lemma fincard.of_equiv {X Y : Type*} (h : X ≃ Y) : fincard' X = fincard' Y :=
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

theorem fincard.of_empty {X : Type*} (hX : X → false) : fincard' X = 0 :=
by simp [fincard.of_equiv (equiv.equiv_empty hX)]

private theorem fincard.prod_of_empty_left {X : Type*} (h : X → false) (Y : Type*) :
  fincard' (X × Y) = fincard' X * fincard' Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.fst), zero_mul]

private theorem fincard.prod_of_empty_right (X : Type*) {Y : Type*} (h : Y → false) :
  fincard' (X × Y) = fincard' X * fincard' Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.snd), mul_zero]

private theorem fincard.prod_of_finite {X Y : Type*}
  (hX : nonempty (fintype X)) (hY : nonempty (fintype Y)) :
fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  unfreezingI {cases hX with hX, cases hY with hY},
  -- change this to squeeze_simp and watch Lean time out
  simp [←card_eq_fincard],
end

private theorem fincard.prod_of_infinite_left {X Y : Type*}
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

private theorem fincard.prod_of_infinite_right {X Y : Type*}
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

theorem fincard.prod (X Y : Sort*) : fincard' (X × Y) = fincard' X * fincard' Y :=
begin
  by_cases hX : X → false,
  { exact fincard.prod_of_empty_left hX _},
  rw [←not_nonempty_iff_imp_false, not_not] at hX,
  by_cases hY : Y → false,
  { exact fincard.prod_of_empty_right _ hY},
  rw [←not_nonempty_iff_imp_false, not_not] at hY,
  by_cases hX2 : nonempty (fintype X),
  { by_cases hY2 : nonempty (fintype Y),
    { exact fincard.prod_of_finite hX2 hY2},
    { exact fincard.prod_of_infinite_right hX hY2},
  },
  { exact fincard.prod_of_infinite_left hX2 hY}
end

lemma card_eq_sum_one {X : Type u} [h : fintype X] : fincard' X = ∑ x : X, 1 :=
begin
  rw [eq_finset_card, finset.card_univ, finsum_def_of_finite],
  unfold univ',
  rw dif_pos (nonempty.intro h),
  simp only [mul_one, nat.cast_id, nsmul_eq_mul, sum_const],
  congr'
end

lemma sum_const {X Y : Type} [fintype X] [add_comm_monoid Y] 
  (s : set X) (m : Y) : ∑ x ∈ s, m = fincard' s •ℕ m := 
by rw [finsum_in_def_of_finite, finset.sum_const m, ←eq_finset_card' s]

lemma sum_const_nat {X : Type} [fintype X] {s : set X} {m : ℕ} {f : X → ℕ} 
  (h : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = fincard' s * m :=
begin
  rw [←nat.nsmul_eq_mul, ←(sum_const s m)],
  exact finsum_ext rfl h
end

theorem card_eq_sum_partition {X : Type} [fintype X] (s : set (set X)) 
  (hS : setoid.is_partition s) : fincard' X = ∑ x ∈ s, fincard' x := 
begin
  rw [eq_finset_card, finsum_in_def_of_finite], -- How is lean able to infer s.finite
  simp_rw [eq_finset_card],
  conv_rhs { congr, skip, funext, rw card_eq_sum_ones },
  --change _ = univ.card = s.to_finset.sum (λ x, x.to_finset.sum (λ _, 1)),
  --rw [←finset.sum_bind _],
  
  /- rw [eq_card', ←hS.sUnion_eq_univ],
  simp_rw eq_card,
  unfold card,
  rw sum_disjoint hS.pairwise_disjoint, refl, -/
  sorry
end

lemma sum_fibres (X Y : Type) (f : X → Y) [fintype X] :
  ∑ y : Y, fincard' (f⁻¹' {y}) = fincard' X :=
begin
  sorry
end

end fincard

--  fincard X = finsum y : Y, fincard (f⁻¹ y)

/-
-- f : X → Y
-- y : range f
-- ∀ a : range f, f⁻¹ a ≃ f⁻¹ y
-- Then card (range f) * card (f⁻¹ y) = card X

-- f : X → Y
-- £X = ∑ y : Y, £(f⁻¹ y) -- assume X finite

lemma sum_fibres (X Y : Type) (f : X → Y) [fintype X] :
  fincard X = finsum y : Y, fincard (f⁻¹ y)

sum_const : sum Y (λ x, c) = c * card

card_equiv

-/
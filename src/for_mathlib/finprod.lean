import order.conditionally_complete_lattice
import algebra.big_operators.basic
import algebra.group.prod
import data.set.finite

universes u v w x y

open_locale classical big_operators

namespace function

-- Some basic lemmas for copied from support

variables {α : Type u} {β : Type v} {ι : Sort w} {A : Type x} {B : Type y}

@[to_additive]
def one_support [has_one A] (f : α → A) : set α := {x | f x ≠ 1}

@[to_additive]
lemma nmem_one_support [has_one A] {f : α → A} {x : α} :
  x ∉ one_support f ↔ f x = 1 :=
classical.not_not

@[to_additive]
lemma mem_one_support [has_one A] {f : α → A} {x : α} :
  x ∈ one_support f ↔ f x ≠ 1 :=
iff.rfl

@[to_additive]
lemma one_support_subset_iff [has_one A] {f : α → A} {s : set α} :
  one_support f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
iff.rfl

@[to_additive]
lemma one_support_subset_iff' [has_one A] {f : α → A} {s : set α} :
  one_support f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
forall_congr $ λ x, by classical; exact not_imp_comm

end function

namespace fin

noncomputable theory

@[to_additive]
noncomputable def prod {ι α} [comm_monoid α] (f : ι → α) : α :=
if h : (function.one_support f).finite then ∏ x in h.to_finset, f x else 1

#print sum
@[to_additive]
noncomputable def prod_in {ι α} [comm_monoid α] (s : set ι) (f : ι → α) : α :=
prod (λ i, if i ∈ s then f i else 1)

notation `∏ ` binder ` ∈ ` s `, ` r:(scoped:67 f, prod_in s f) := r
notation `∏ ` binder `, ` r:(scoped:67 f, prod f) := r
notation `∑ ` binder ` ∈ ` s `, ` r:(scoped:67 f, sum_in s f) := r
notation `∑ ` binder `, ` r:(scoped:67 f, sum f) := r

end fin

def finset.univ' (ι : Type*) : finset ι := if h : nonempty (fintype ι) then
  (classical.choice h).elems else ∅

namespace finset 

lemma univ'_eq_univ_of_finitype {ι : Type u} [h : fintype ι] : univ' ι = univ :=
begin
  unfold univ', unfold univ,
  convert dif_pos (nonempty.intro h)
end

lemma mem_univ' {ι : Type u} [fintype ι] (x : ι) : x ∈ univ' ι :=
begin
  rw univ'_eq_univ_of_finitype, 
  exact mem_univ _
end

end finset

namespace fin

open finset

variables {ι : Type u} {α : Type v} [comm_monoid α]
variables {f : ι → α}

@[to_additive]
lemma prod_in_eq_finset_prod (f : ι → α) (s : finset ι) :
  ∏ x ∈ ↑s, f x = s.prod f :=
begin
  unfold prod_in, 
  unfold prod,
  rw dif_pos,
  { rw [finset.prod_ite, prod_const_one, mul_one],
    refine finset.prod_subset _ _,
    { apply set.finite.subset (s.finite_to_set),
      rintro x h,
      rw function.mem_one_support at h,
      split_ifs at h, assumption, contradiction },
    { intro _, simp only [and_imp, mem_filter, imp_self, mem_coe, forall_true_iff] },
    { simp only [function.mem_one_support, mem_filter, and_true, if_true, 
        set.finite.mem_to_finset, mem_coe, eq_self_iff_true,
        classical.not_not, forall_true_iff] { contextual := tt } } },
end

@[to_additive]
lemma prod_in_eq_prod (f : ι → α) (s : set ι) :
  ∏ x ∈ s, f x = ∏ x : s, f x := sorry

@[to_additive]
lemma prod_in_def_of_finite' {f : ι → α} (s : set ι) 
  (hf : (function.one_support f).finite) : 
  ∏ x ∈ s, f x = (filter (∈ s) hf.to_finset).prod f := 
begin
  unfold prod_in, unfold prod,
  rw dif_pos,
    { rw [prod_ite, prod_const_one, mul_one],
      refine finset.prod_subset _ _,
        { refine set.finite.subset hf (λ x hx, _),
          rw function.mem_one_support at ⊢ hx,
          intro h, apply hx,
          split_ifs, exact h, refl },
        { intros x hx,
          rw mem_filter at ⊢ hx,
          cases hx with hx₀ hx₁,
          refine ⟨_, hx₁⟩,
          rw [set.finite.mem_to_finset, function.mem_one_support, if_pos hx₁] at hx₀,
          rw set.finite.mem_to_finset, exact hx₀ },
    { simp [function.mem_one_support] {contextual := tt} } }
end .

-- ↓ Rewrite below as a corollary of `prod_in_def_of_finite'`
@[to_additive]
lemma prod_in_def_of_finite [fintype ι] (f : ι → α) (s : set ι) : 
  ∏ x ∈ s, f x = s.to_finset.prod f := 
begin
  unfold prod_in,
  unfold prod,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  rw [finset.prod_ite, prod_const_one, mul_one],
  refine finset.prod_subset _ _,
  { intro x, simp only [and_imp, mem_filter, imp_self, set.mem_to_finset, forall_true_iff]},
  { simp only [function.mem_one_support, mem_filter, and_true, if_true, set.finite.mem_to_finset, set.mem_to_finset, eq_self_iff_true,
 classical.not_not, forall_true_iff] {contextual := tt} }
end

@[to_additive]
lemma prod_def_of_finite [h : fintype ι] (f : ι → α) : 
  ∏ x : ι, f x = (finset.univ' ι).prod f :=
begin
  unfold prod,
  rw dif_pos (set.finite.of_fintype (_ : set ι)),
  refine finset.prod_subset (λ _ _, mem_univ' _) _,
    intros _ _ hx, 
    rw ←function.nmem_one_support,
    simpa using hx,
end

@[to_additive]
lemma prod_def_of_finite' {f : ι → α} (hf : (function.one_support f).finite) : 
  ∏ x : ι, f x = hf.to_finset.prod f :=
begin
  unfold prod,
  rw dif_pos hf
end

@[to_additive]
lemma prod_def_of_infinite {f : ι → α} (hf : ¬(function.one_support f).finite) : 
  ∏ x : ι, f x = 1 :=
begin
  unfold prod,
  rw dif_neg hf
end

@[to_additive]
lemma prod_eq_prod_in_univ (f : ι → α) : 
  ∏ x : ι, f x = ∏ x ∈ set.univ, f x :=
begin
  by_cases ((function.one_support f).finite),
    { rw [prod_def_of_finite' h, prod_in_def_of_finite' _ h], simp },
    { unfold prod_in,
      rw [prod_def_of_infinite h, prod_def_of_infinite], simpa }
end

@[to_additive]
lemma prod_ext {s t : set ι} {f₁ f₂ : ι → α} (h₀ : s = t) 
  (h₁ : ∀ x ∈ t, f₁ x = f₂ x) : ∏ x ∈ s, f₁ x = ∏ x ∈ t, f₂ x :=
begin
  subst h₀,
  unfold prod_in,
  congr',
  ext x,
  split_ifs,
  { exact h₁ x h },
  { refl },
end

@[to_additive]
lemma prod_union [fintype ι] {s t : set ι} (f : ι → α) (h : disjoint s t) : 
  ∏ x ∈ (s ∪ t), f x = (∏ x ∈ s, f x) * ∏ x ∈ t, f x :=
begin
  iterate 3 { rw prod_in_def_of_finite },
  rw ←finset.prod_union, congr', 
    { ext, simp }, 
    { intros a ha,
      apply @h a,
      simpa using ha }
end

@[to_additive]
lemma prod_bind {γ} [fintype γ] [fintype ι] {s : set γ} {t : γ → set ι} 
  (f : ι → α) (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) : 
  (∏ x ∈ (⋃ x ∈ s, t x), f x) = ∏ x ∈ s, ∏ i ∈ t x, f i :=
begin
  iterate 2 { rw prod_in_def_of_finite },
  conv_rhs { congr, skip, funext, rw prod_in_def_of_finite },
    { convert @prod_bind _ _ _ f _ _ s.to_finset (λ x, (t x).to_finset) 
      (begin
        intros x hx y hy hxy a ha,
        specialize h x (set.mem_to_finset.1 hx) y (set.mem_to_finset.1 hy) hxy,
        apply @h a, simpa using ha end),
      { ext, rw [mem_bind, set.mem_to_finset, set.mem_bUnion_iff],
        split; intro ha; rcases ha with ⟨x, hx₀, hx₁⟩,
          exact ⟨x, set.mem_to_finset.2 hx₀, set.mem_to_finset.2 hx₁⟩,
          exact ⟨x, set.mem_to_finset.1 hx₀, set.mem_to_finset.1 hx₁⟩ } },
end

end fin
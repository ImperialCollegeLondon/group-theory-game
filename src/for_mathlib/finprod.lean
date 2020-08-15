import order.conditionally_complete_lattice
import algebra.big_operators.basic
import algebra.group.prod

universes u v w x y

open set
open_locale big_operators
namespace function

variables {α : Type u} {β : Type v} {ι : Sort w} {A : Type x} {B : Type y}

@[to_additive]
def one_support [has_one A] (f : α → A) : set α := {x | f x ≠ 1}

@[to_additive]
lemma one_nmem_one_support' [has_one A] {f : α → A} {x : α} :
  x ∉ one_support f ↔ f x = 1 :=
classical.not_not

@[to_additive]
lemma one_mem_one_support [has_one A] {f : α → A} {x : α} :
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

@[to_additive]
lemma one_support_binop_subset [has_one A] (op : A → A → A) (op1 : op 1 1 = 1) (f g : α → A) :
  one_support (λ x, op (f x) (g x)) ⊆ one_support f ∪ one_support g :=
λ x hx, classical.by_cases
  (λ hf : f x = 1, or.inr $ λ hg, hx $ by simp only [hf, hg, op1])
  or.inl

@[to_additive]
lemma one_support_add [monoid A] (f g : α → A) :
  one_support (λ x, f x * g x) ⊆ one_support f ∪ one_support g :=
one_support_binop_subset (*) (one_mul _) f g

@[simp, to_additive]
lemma one_support_inv [group A] (f : α → A) :
  one_support (λ x, (f x)⁻¹) = one_support f :=
set.ext $ λ x, not_congr inv_eq_one

#exit
lemma one_support_sub [group A] (f g : α → A) :
  one_support (λ x, f x * (g x)⁻¹) ⊆ one_support f ∪ one_support g :=
one_support_binop_subset (has_sub.sub) (sub_self _) f g

@[simp] lemma one_support_mul [mul_zero_class A] [no_zero_divisors A] (f g : α → A) :
  one_support (λ x, f x * g x) = one_support f ∩ one_support g :=
set.ext $ λ x, by simp only [one_support, ne.def, mul_eq_zero, mem_set_of_eq,
  mem_inter_iff, not_or_distrib]

@[simp] lemma one_support_inv [division_ring A] (f : α → A) :
  one_support (λ x, (f x)⁻¹) = one_support f :=
set.ext $ λ x, not_congr inv_eq_zero

@[simp] lemma one_support_div [division_ring A] (f g : α → A) :
  one_support (λ x, f x / g x) = one_support f ∩ one_support g :=
by simp [div_eq_mul_inv]

lemma one_support_sup [has_one A] [semilattice_sup A] (f g : α → A) :
  one_support (λ x, (f x) ⊔ (g x)) ⊆ one_support f ∪ one_support g :=
one_support_binop_subset (⊔) sup_idem f g

lemma one_support_inf [has_one A] [semilattice_inf A] (f g : α → A) :
  one_support (λ x, (f x) ⊓ (g x)) ⊆ one_support f ∪ one_support g :=
one_support_binop_subset (⊓) inf_idem f g

lemma one_support_max [has_one A] [decidable_linear_order A] (f g : α → A) :
  one_support (λ x, max (f x) (g x)) ⊆ one_support f ∪ one_support g :=
one_support_sup f g

lemma one_support_min [has_one A] [decidable_linear_order A] (f g : α → A) :
  one_support (λ x, min (f x) (g x)) ⊆ one_support f ∪ one_support g :=
one_support_inf f g

lemma one_support_supr [has_one A] [conditionally_complete_lattice A] [nonempty ι] (f : ι → α → A) :
  one_support (λ x, ⨆ i, f i x) ⊆ ⋃ i, one_support (f i) :=
begin
  intros x hx,
  classical,
  contrapose hx,
  simp only [mem_Union, not_exists, nmem_one_support] at hx ⊢,
  simp only [hx, csupr_const]
end

lemma one_support_infi [has_one A] [conditionally_complete_lattice A] [nonempty ι] (f : ι → α → A) :
  one_support (λ x, ⨅ i, f i x) ⊆ ⋃ i, one_support (f i) :=
@one_support_supr _ _ (order_dual A) ⟨(1:A)⟩ _ _ f

lemma one_support_sum [add_comm_monoid A] (s : finset α) (f : α → β → A) :
  one_support (λ x, ∑ i in s, f i x) ⊆ ⋃ i ∈ s, one_support (f i) :=
begin
  intros x hx,
  classical,
  contrapose hx,
  simp only [mem_Union, not_exists, nmem_one_support] at hx ⊢,
  exact finset.sum_eq_zero hx
end

lemma one_support_prod_subset [comm_monoid_with_zero A] (s : finset α) (f : α → β → A) :
  one_support (λ x, ∏ i in s, f i x) ⊆ ⋂ i ∈ s, one_support (f i) :=
λ x hx, mem_bInter_iff.2 $ λ i hi H, hx $ finset.prod_eq_zero hi H

lemma one_support_prod [comm_monoid_with_zero A] [no_zero_divisors A] [nontrivial A]
  (s : finset α) (f : α → β → A) :
  one_support (λ x, ∏ i in s, f i x) = ⋂ i ∈ s, one_support (f i) :=
set.ext $ λ x, by
  simp only [one_support, ne.def, finset.prod_eq_zero_iff, mem_set_of_eq, set.mem_Inter, not_exists]

lemma one_support_comp_subset [has_one A] [has_one B] {g : A → B} (hg : g 1 = 1) (f : α → A) :
  one_support (g ∘ f) ⊆ one_support f :=
λ x, mt $ λ h, by simp [(∘), *]

lemma one_support_subset_comp [has_one A] [has_one B] {g : A → B} (hg : ∀ {x}, g x = 1 → x = 1)
  (f : α → A) :
  one_support f ⊆ one_support (g ∘ f) :=
λ x, mt hg

lemma one_support_comp_eq [has_one A] [has_one B] (g : A → B) (hg : ∀ {x}, g x = 1 ↔ x = 1)
  (f : α → A) :
  one_support (g ∘ f) = one_support f :=
set.ext $ λ x, not_congr hg

lemma one_support_prod_mk [has_one A] [has_one B] (f : α → A) (g : α → B) :
  one_support (λ x, (f x, g x)) = one_support f ∪ one_support g :=
set.ext $ λ x, by simp only [one_support, classical.not_and_distrib, mem_union_eq, mem_set_of_eq,
  prod.mk_eq_zero, ne.def]

end function

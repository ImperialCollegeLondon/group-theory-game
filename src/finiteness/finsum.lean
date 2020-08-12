import data.finsupp finiteness.is_finite

open_locale classical

noncomputable def finsum {ι α} [add_comm_monoid α] (f : ι → α) : α :=
if h : ∃ f' : ι →₀ α, f = f' then (classical.some h).sum (λ _ a, a) else 0

noncomputable def finsum_in {ι α} [add_comm_monoid α] (s : set ι) (f : ι → α) : α :=
finsum (λ i, if i ∈ s then f i else 0)

notation `∑` binder ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r

namespace is_finite

variables {α β : Type} [add_comm_monoid β]
variables {f : α → β}

def finsum_def_of_finite [h : is_finite α] (f : α → β) : 
  finsum f = (@finset.univ α (to_fintype α)).sum f := sorry

noncomputable instance [is_finite α] (s : set α) : fintype s := 
by haveI := to_fintype α; apply_instance

def finsum_in_def_of_finite [h : is_finite α] (f : α → β) (s : set α): 
  ∑ x ∈ s, f x = s.to_finset.sum f := sorry

lemma finsum_ext {s t : set α} {f₁ f₂ : α → β} (h₀ : s = t) 
  (h₁ : ∀ x ∈ t, f₁ x = f₂ x) : ∑ x ∈ s, f₁ x = ∑ x ∈ t, f₂ x := sorry

end is_finite
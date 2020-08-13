import data.finsupp finiteness.is_finite

open_locale classical big_operators

noncomputable def finsum {ι α} [add_comm_monoid α] (f : ι → α) : α :=
if h : ∃ f' : ι →₀ α, f = f' then (classical.some h).sum (λ _ a, a) else 0

noncomputable def finsum_in {ι α} [add_comm_monoid α] (s : set ι) (f : ι → α) : α :=
finsum (λ i, if i ∈ s then f i else 0)

notation `∑` binder ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r

lemma is_finite_supp {α β} [has_zero β] (f : α →₀ β) : is_finite {a | f a ≠ 0} :=
sorry

namespace is_finite

open finset finsupp

variables {ι α : Type} [is_finite ι] [add_comm_monoid α]
variables {f : ι → α}

noncomputable def finsupp_of_is_finite (f : ι → α) : ι →₀ α := 
    { support := filter (λ x, f x ≠ 0) $ @univ ι (to_fintype ι),
      to_fun := f,
      mem_support_to_fun := λ _, 
        ⟨λ h, (mem_filter.1 h).2, λ h, mem_filter.2 ⟨@mem_univ _ (to_fintype ι) _, h⟩⟩}

@[simp] lemma finsupp_of_is_finite_eq (f : ι → α) : 
  (finsupp_of_is_finite f : ι → α) = f := rfl

lemma finsum_def_of_finite (f : ι → α) : 
  finsum f = (finsupp_of_is_finite f).sum (λ _ a, a) := 
begin
  unfold finsum,
  have h : ∃ (f' : ι →₀ α), f = f' := ⟨finsupp_of_is_finite f, rfl⟩,
  rw dif_pos h,
  congr, ext, rw finsupp_of_is_finite_eq,
  solve_by_elim [(classical.some_spec h).symm],
end

#exit
noncomputable instance (s : set ι) : fintype s := 
by haveI := to_fintype ι; apply_instance

-- (on_finset s f hf).sum g = ∑ a in s, g a (f a) :=

lemma finsum_in_def_of_finite (f : ι → α) (s : set ι) : 
  ∑ x ∈ s, f x = s.to_finset.sum f := 
begin
  unfold finsum_in,
  rw finsum_def_of_finite,
  rw sum_fintype _ _ (sorry),
end

lemma finsum_ext {s t : set ι} {f₁ f₂ : ι → α} (h₀ : s = t) 
  (h₁ : ∀ x ∈ t, f₁ x = f₂ x) : ∑ x ∈ s, f₁ x = ∑ x ∈ t, f₂ x := sorry

end is_finite
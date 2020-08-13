import hom.quotient data.setoid.partition
#exit
/- I think we've decided to change:
- fintype → is_finite
- set.card → fincard
-/

--open_locale classical big_operators

--notation `∑` binder ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r
localized "notation `∑` binder ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r" in finsum
localized "notation `∑` binders `, ` r:(scoped:67 f, finsum f) := r" in finsum

--localized "notation `∑` binders ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r" in finsum
--localized "notation `∑` binders ` ∈ ` s `, ` r:(scoped:67 f, finsum_in s f) := r" in finsum

open_locale finsum

open setoid set

namespace fincard

variables {α β : Type} [comm_semiring β]

lemma card_eq_sum_ones [is_finite α] (s : set α) : 
  fincard s = ∑ x ∈ s, 1 := sorry

-- Question: we have is_finite α but we need finite s. Should we create an instance 
-- or should we not use set.sum at all-
lemma sum_const [is_finite α] (s : set α) (m : β) :
  ∑ x ∈ s, m = m * fincard s := 
begin
  rw card_eq_sum_ones, 
  sorry
end

lemma sum_const_nat [is_finite α] {s : set α} {m : ℕ} {f : α → ℕ} (h : ∀ x ∈ s, f x = m) :
  ∑ x ∈ s, f x = m * fincard s :=
begin
  sorry
  /- have := sum_const s m,
  norm_cast at this, -- This is annoying
  rw ←this,
  exact sum_ext rfl h -/
end

theorem card_eq_sum_partition [is_finite α] (s : set (set α)) (hS : is_partition s) : 
  fincard α = ∑ x ∈ s, fincard x := 
begin
  sorry
  /- rw [eq_card', ←hS.sUnion_eq_univ],
  simp_rw eq_card,
  unfold card,
  rw sum_disjoint hS.pairwise_disjoint, refl, -/
end

end fincard

namespace mygroup 

namespace lagrange

open mygroup.quotient mygroup.subgroup fincard

variables {G : Type} [group G] {H : subgroup G}

def lcoset_setoid (H : subgroup G) : setoid G := 
{ r := lcoset_rel H,
  iseqv := lcoset_iseqv H }

lemma lcoset_setoid_classes : 
  (lcoset_setoid H).classes = { B | ∃ g : G, B = lcoset g H } :=
begin
  ext, split; rintro ⟨g, rfl⟩; refine ⟨g, _⟩, apply eq.symm,
  all_goals { show _ = { h | lcoset_rel H h g },
              ext, split; intro hx,
                { exact lcoset_digj (self_mem_coset x H) hx },
                { rw [mem_set_of_eq, lcoset_rel_def] at hx,
                  rw ←hx, exact self_mem_coset _ _ } }
end

/-- The left cosets of a subgroup `H` form a partition -/
def lcoset_partition (H : subgroup G) : 
  is_partition { B | ∃ g : G, B = lcoset g H } := 
begin
  rw ←lcoset_setoid_classes,
  exact is_partition_classes (lcoset_setoid H)
end

/-- Let `H` be a subgroup of the finite group `G`, then the cardinality of `G` 
equals the cardinality of `H` multiplied with the number of left cosets of `H` -/
theorem lagrange [is_finite G] : 
  fincard G = fincard H * fincard { B | ∃ g : G, B = lcoset g H } := 
begin
  rw card_eq_sum_partition _ (lcoset_partition H), sorry
  --refine sum_const_nat (λ _ hx, _), 
  --rcases hx with ⟨g, rfl⟩, 
  --exact eq_card_of_lcoset.symm
end

end lagrange

end mygroup
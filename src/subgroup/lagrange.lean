import hom.quotient data.setoid.partition for_mathlib.finsum

/- I think we've decided to change:
- fintype → is_finite
- set.card → fincard
-/

open setoid set

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
theorem lagrange [fintype G] : 
  fincard' G = fincard' H * fincard' { B | ∃ g : G, B = lcoset g H } := 
begin
  sorry
  --rw card_eq_sum_partition _ (lcoset_partition H), 
  --refine sum_const_nat (λ _ hx, _), 
  --rcases hx with ⟨g, rfl⟩, 
  --exact eq_card_of_lcoset.symm
end

end lagrange

end mygroup
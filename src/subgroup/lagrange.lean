import hom.quotient data.setoid.partition for_mathlib.finite_stuff

notation `∑` binder ` in ` s `, ` r:(scoped:67 f, s.sum f) := r

open set

lemma fincard.eq_card {α} (s : set α) : fincard s = card s := sorry

namespace mygroup 

namespace lagrange

open setoid mygroup.quotient subgroup set fincard

variables {G : Type} [group G] {H : subgroup G}

def lcoset_setoid (H : subgroup G) : setoid G := 
{ r := lcoset_rel H,
  iseqv := lcoset_iseqv H }

lemma lcoset_setoid_classes : 
  (lcoset_setoid H).classes = { B | ∃ g : G, B = g • H } :=
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
  is_partition { B | ∃ g : G, B = g • H } := 
begin
  rw ←lcoset_setoid_classes,
  exact is_partition_classes (lcoset_setoid H)
end

-- ↓ this is not true
theorem card_eq_sum_partition {α} (s : set (set α)) (hS : is_partition s) : 
  fincard α = ∑ x in s, fincard x := 
begin
  sorry,
end

lemma sum_const_nat {α} {s : set α} {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) :
  (∑ x in s, f x) = fincard s * m :=
begin
  rw [eq_card, mul_comm],
  have := sum_const s m,
  norm_cast at this, -- This is annoying
  rw ←this,
  exact sum_ext rfl h₁,
end

/-- Let `H` be a subgroup of the finite group `G`, then the cardinality of `G` 
equals the cardinality of `H` multiplied with the number of left cosets of `H` -/
theorem lagrange : 
  fincard G = fincard { B | ∃ g : G, B = g • H } * fincard H := 
begin
  rw card_eq_sum_partition _ (lcoset_partition H),
  refine sum_const_nat (λ _ hx, _), 
  rcases hx with ⟨g, rfl⟩, 
  exact eq_card_of_lcoset.symm
end

end lagrange

end mygroup
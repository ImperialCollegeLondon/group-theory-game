import hom.quotient data.setoid.partition for_mathlib.finsum

open setoid set

namespace fincard

variables {α β : Type}

lemma eq_card (s : set α) : fincard s = card s := sorry
lemma eq_card' : fincard α = card (univ : set α) := sorry

lemma sum_const [comm_semiring β] (s : set α) (m : β):
  ∑ x in s, (λ x, m) x = m * fincard s := sorry -- by rw [eq_card, set.sum_const s m]

lemma sum_const_nat {s : set α} {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) :
  ∑ x in s, f x = m * fincard s :=
begin
  have := sum_const s m,
  norm_cast at this, -- This is annoying
  rw ←this,
  exact sum_ext rfl h₁,
end

theorem card_eq_sum_partition [fintype α] (s : set (set α)) (hS : is_partition s) : 
  fincard α = ∑ x in s, fincard x := 
begin
  rw [eq_card', ←hS.sUnion_eq_univ],
  simp_rw eq_card,
  unfold card,
  rw sum_disjoint hS.pairwise_disjoint, refl,
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
theorem lagrange [fintype G] : 
  fincard G = fincard H * fincard { B | ∃ g : G, B = g • H } := 
begin
  rw [card_eq_finsum_partition _ (lcoset_partition H), 
    mul_comm, finsum_const_nat],
  rintros x ⟨g, rfl⟩,
  exact eq_card_of_lcoset.symm
end

end lagrange

end mygroup
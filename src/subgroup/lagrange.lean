import hom.quotient data.setoid.partition

open setoid set

namespace mygroup 

namespace lagrange

open mygroup.quotient mygroup.subgroup fincard function

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
  rw [card_eq_finsum_partition (lcoset_partition H), 
    mul_comm, finsum_const_nat],
  rintros x ⟨g, rfl⟩,
  exact eq_card_of_lcoset.symm
end

def to_lcosets (N : normal G) : G /ₘ N → { B | ∃ g : G, B = lcoset g N } :=
λ x, let f : G → { B | ∃ g : G, B = lcoset g N } := λ g, ⟨g ⋆ N, ⟨g, rfl⟩⟩ in 
  lift_on x f (λ a b h, by simpa [h])

lemma to_lcosets_mk {N : normal G} (g : G) : 
  (to_lcosets N (g : G /ₘ N)).val = lcoset g N := rfl

lemma bijective_to_lcosets {N : normal G} : bijective (to_lcosets N) :=
begin
  split,
    { intros x y hxy,
      rcases exists_mk x with ⟨x, rfl⟩,
      rcases exists_mk y with ⟨y, rfl⟩,
      rw [mk_eq, ← to_lcosets_mk, hxy, to_lcosets_mk] },
    { rintro ⟨_, g, rfl⟩, exact ⟨g, subtype.eq (to_lcosets_mk g)⟩ }
end

noncomputable def to_lcosets_equiv (N : normal G) : 
  G /ₘ N ≃ { B | ∃ g : G, B = lcoset g N } :=
equiv.of_bijective (to_lcosets N) bijective_to_lcosets

theorem card_quotient_eq_mul [fintype G] (N : normal G) : 
  fincard' G = fincard' N * fincard' (G /ₘ N) :=
begin
  rw @lagrange _ _ (N : subgroup G),
  congr' 1, exact of_equiv (to_lcosets_equiv N).symm
end

end lagrange

end mygroup
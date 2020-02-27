import subgroup.definitions

/-
An API for subgroups

Mathematician-friendly

Let G be a group. The type of subgroups of G is `subgroup G`. 
In other words, if `H : subgroup G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min (and even sup and inf). 
-/

-- This entire project takes place in the `mygroup` namespace
namespace mygroup

-- TODO: prove subgroups are a lattice/semilattice-sup-bot/complete lattice/ whatever

namespace subgroup

variables {G : Type}
variables [group G]

-- If a statement if true about group G, then its true for its subgroups
theorem group_props {K : subgroup G} (hprop : G → Prop) : 
(∀ g : G, hprop g = true) → ∀ k ∈ K, hprop k = true := λ hg k hk, hg k

-- Some equivalent definitions for normal groups from wikipedia
-- Any two elements commute regarding the normal subgroup membership relation
lemma in_normal_to_comm {K : subgroup G} [normal K] : ∀ g k : G, g * k ∈ K → k * g ∈ K :=
begin
    intros g k hgk,
    suffices : g⁻¹ * (g * k) * g ∈ K,
        {rwa [←group.mul_assoc, group.mul_left_inv, group.one_mul] at this},
    convert normal.conjugate g⁻¹ (g * k) hgk, rw group.inv_inv
end

lemma comm_to_in_normal {K : subgroup G} (h : ∀ g k : G, g * k ∈ K → k * g ∈ K) : normal K :=
begin
    split,
    intros g k hk,
    suffices : g * (k * g⁻¹) ∈ K,
        {rwa ←group.mul_assoc at this},
    apply h (k * g⁻¹) g,
    rwa [group.mul_assoc, group.mul_left_inv, group.mul_one]
end

-- If K is a normal subgroup of the group G, then the sets of left and right cosets of K in the G coincide
lemma nomal_coset_eq {K : subgroup G} [normal K] : 
∀ g : G, left_coset g K = right_coset g K :=
begin
    intros g,
    ext, split,
        all_goals {repeat {rw set.mem_set_of_eq}, intros hx, rcases hx with ⟨k, ⟨hk₁, hk₂⟩⟩},
        {use (g * k * g⁻¹), split,
        all_goals {try {apply normal.conjugate, assumption}},
        rwa [←hk₂, group.mul_assoc, group.mul_left_inv, group.mul_one]
        },
        use (g⁻¹ * k * g), split,
        convert normal.conjugate g⁻¹ k hk₁, rwa group.inv_inv,
        rwa [←group.mul_assoc, ←group.mul_assoc, group.mul_right_inv, group.one_mul, hk₂]
end

lemma coset_eq_normal {K : subgroup G} (h : ∀ g : G, left_coset g K = right_coset g K) : normal K :=
begin
    split,
    intros g k hk,
    replace h : {s : G | ∃ (k : G) (H : k ∈ K), s = g * k} = {s : G | ∃ (k : G) (H : k ∈ K), s = k * g} := h g,
    have : ∃ s ∈ {s : G | ∃ k ∈ K, s = k * g}, s = g * k :=
        by {rw ←h, use (g * k),
        simp only [group.mul_right_cancel_iff, exists_prop, and_true, set.mem_set_of_eq],
        split, use k, from ⟨hk, rfl⟩, refl
        },
    rcases this with ⟨s, ⟨hs₁, hs₂⟩⟩,
    rw set.mem_set_of_eq at hs₁,
    rcases hs₁ with ⟨l, ⟨hl₁, hl₂⟩⟩,
    rw [←hs₂, hl₂, group.mul_assoc, group.mul_right_inv, group.mul_one],
    assumption
end

-- If K is a normal subgroup of the group G then the product of an element of the left coset of K with respect to g ∈ G and an element of the left coset of N with respect to h ∈ G is an element of the left coset of K with respect to gh
lemma normal_to_prod_in_coset {K : subgroup G} [normal K] : 
∀ x y g h : G, x ∈ left_coset g K ∧ y ∈ left_coset h K → x * y ∈ left_coset (g * h) K :=
begin
    sorry
end

lemma prod_in_coset_to_normal {K : subgroup G} 
(h : ∀ x y g h : G, x ∈ left_coset g K ∧ y ∈ left_coset h K → x * y ∈ left_coset (g * h) K) : normal K :=
begin
    sorry
end

/-
TODO : Normal K equivalent to
- K is a union of conjugate classes
- K is preserved by inner automorphisms
-/

end subgroup

end mygroup
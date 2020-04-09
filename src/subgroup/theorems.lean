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

-- The intersect of two subgroups is also a subgroup
def inter_subgroup (H K : subgroup G) : subgroup G :=
{ carrier := H ∩ K,
  one_mem' := ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩, 
    ⟨H.mul_mem hhx hhy, K.mul_mem hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
    ⟨H.inv_mem hhx, K.inv_mem hhy⟩}

open set
variable {ι : Sort}

-- The intersect of a set of subgroups is a subgroup
def Inter_subgroup (H : ι → subgroup G) : subgroup G := 
{ carrier := ⋂ i, H i,
  one_mem' := mem_Inter.mpr $ λ i, (H i).one_mem,
  mul_mem' := λ _ _ hx hy, mem_Inter.mpr $ λ i, 
    by {rw mem_Inter at *, from mul_mem (H i) (hx i) (hy i)},
  inv_mem' := λ x hx, mem_Inter.mpr $ λ i, (H i).inv_mem $ by apply mem_Inter.mp hx }


-- Some equivalent definitions for normal groups from wikipedia
-- Any two elements commute regarding the normal subgroup membership relation
lemma in_normal_to_comm {K : subgroup G} [normal K] : ∀ g k : G, g * k ∈ K → k * g ∈ K :=
begin
    intros g k hgk,
    suffices : g⁻¹ * (g * k) * g ∈ K,
        {rwa [←group.mul_assoc, group.mul_left_inv, group.one_mul] at this},
    convert normal.conjugate g⁻¹ (g * k) hgk, rw group.inv_inv
end

instance comm_to_in_normal {K : subgroup G} (h : ∀ g k : G, g * k ∈ K → k * g ∈ K) : normal K :=
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

instance coset_eq_normal {K : subgroup G} (h : ∀ g : G, left_coset g K = right_coset g K) : normal K :=
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
    rintros x y g h ⟨hx, hy⟩,
    rw set.mem_set_of_eq at hx hy,
    rcases hx with ⟨k₀, ⟨hx₁, hx₂⟩⟩,
    rcases hy with ⟨k₁, ⟨hy₁, hy₂⟩⟩,
    rw [hx₂, hy₂],
    suffices : h⁻¹ * k₀ * h * k₁ ∈ K,
        {rw set.mem_set_of_eq,
        use h⁻¹ * k₀ * h * k₁,
        split, assumption,
        apply group.mul_left_cancel g⁻¹,
        rw [←@group.mul_assoc _ _ g⁻¹ (g * k₀) (h * k₁), ←@group.mul_assoc _ _ g⁻¹ g k₀, 
        group.mul_left_inv, group.one_mul,
        ←@group.mul_assoc _ _ g⁻¹ (g * h) (h⁻¹ * k₀ * h * k₁), ←@group.mul_assoc _ _ g⁻¹ g h, 
        group.mul_left_inv, group.one_mul],
        apply group.mul_left_cancel h⁻¹,
        rw [←@group.mul_assoc _ _ h⁻¹ h  (h⁻¹ * k₀ * h * k₁), group.mul_left_inv, group.one_mul,
        ←@group.mul_assoc _ _ h⁻¹ k₀ (h * k₁), ←@group.mul_assoc _ _ (h⁻¹ * k₀) h k₁]
        },
    apply @mul_mem _ _ K (h⁻¹ * k₀ * h) k₁,
    convert normal.conjugate h⁻¹ k₀ hx₁, 
        rw group.inv_inv,
        assumption
end

instance prod_in_coset_to_normal {K : subgroup G} 
(h : ∀ x y g h : G, x ∈ left_coset g K ∧ y ∈ left_coset h K → x * y ∈ left_coset (g * h) K) : normal K :=
begin
    split, intros g k hk,
    let x := g * k,
    let y :=  g⁻¹ * k,
    suffices : g * k * g⁻¹ * k ∈ K,
        {rw [←group.mul_one (g * k * g⁻¹), ←group.mul_right_inv k, ←group.mul_assoc],
        apply mul_mem, assumption,
        apply inv_mem, assumption
        },
    suffices : g * k * g⁻¹ * k ∈ left_coset (g * g⁻¹) K,
        {rw [set.mem_set_of_eq, group.mul_right_inv] at this,
        rcases this with ⟨l, ⟨hl₁, hl₂⟩⟩,
        rw [hl₂, group.one_mul], assumption
        },
    rw group.mul_assoc,
    show x * y ∈ left_coset (g * g⁻¹) K,
    apply h x y g g⁻¹,
    split, {use k, from ⟨hk, rfl⟩},
        {use k, from ⟨hk, rfl⟩}
end

/-
TODO : Normal K equivalent to
- K is a union of conjugate classes
-/

-- Trivial central subgroups

end subgroup

end mygroup
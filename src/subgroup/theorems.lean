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

-- Change the above to has_inf and has_Inf respectively so we can use them for 
-- proving they are lattices?

-- Move Lagrange's theorem from orbit.random to here

-- Some equivalent definitions for normal groups from wikipedia
open normal

-- Any two elements commute regarding the normal subgroup membership relation
lemma comm_mem_of_normal {K : normal G} 
  {g k : G} (h : g * k ∈ K) : k * g ∈ K :=
begin
  suffices : k * (g * k) * k⁻¹ ∈ K,
    { simp [group.mul_assoc] at this, assumption },
  refine conj_mem _ _ h _
end

def normal_of_mem_comm {K : subgroup G} 
  (h : ∀ g k : G, g * k ∈ K → k * g ∈ K) : normal G :=
{ conj_mem := 
  begin
    intros n hn g,
    suffices : g * (n * g⁻¹) ∈ K,
      { rwa ←group.mul_assoc at this },
    refine h _ _ _, simpa [group.mul_assoc]
  end, .. K } -- The .. tells Lean that we use K for the unfilled fields

-- If K is a normal subgroup of the group G, then the sets of left and right 
-- cosets of K in the G coincide
lemma nomal_coset_eq {K : normal G} : 
  ∀ g : G, g • (K : subgroup G) = (K : subgroup G) • g :=
begin
  -- dsimp, 
  -- Without the dsimp it displays weridly,
  -- dsimp not required if we write out right_coset g K however?
  intros g,
  ext, split; intro hx,
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g, _⟩,
      simp [group.mul_assoc] },
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g⁻¹, _⟩,
      simp [←group.mul_assoc] }
end

def normal_of_coset_eq {K : subgroup G} 
  (h : ∀ g : G, g • K = K • g) : normal G :=
{ conj_mem := 
  begin
    intros n hn g,
    have : ∃ s ∈ K • g, s = g * n,
      { refine ⟨g * n, _, rfl⟩,
        rw ←h, exact ⟨n, hn, rfl⟩ },
    rcases this with ⟨s, ⟨l, hl₁, hl₂⟩, hs₂⟩,
    rw [←hs₂, hl₂],
    simpa [group.mul_assoc]
  end, .. K}

-- If K is normal then if x ∈ g K and y ∈ h K then x * y ∈ (g * h) K
lemma prod_in_coset_of_normal {K : normal G} {x y g h : G} 
  (hx : x ∈ g • K) (hy : y ∈ h • K) : x * y ∈ (g * h) • K :=
begin
  rcases hx with ⟨k₀, hx₁, rfl⟩,
  rcases hy with ⟨k₁, hy₁, rfl⟩,
  refine ⟨h⁻¹ * k₀ * h * k₁, _, _⟩,
    { refine K.1.3 _ hy₁, 
      convert K.2 _ hx₁ _, exact (group.inv_inv _).symm },
    { iterate 2 { rw group.mul_assoc },
      rw group.mul_left_cancel_iff g _ _,
      simp [←group.mul_assoc] }
end

def normal_of_prod_in_coset {K : subgroup G} 
  (h : ∀ x y g h : G, x ∈ g • K → y ∈ h • K → x * y ∈ (g * h) • K) : normal G :=
{ conj_mem := 
  begin
    intros n hn g,
    rcases h (g * n) (g⁻¹ * n) g g⁻¹ 
      ⟨n, hn, rfl⟩ ⟨n, hn, rfl⟩ with ⟨m, hm₀, hm₁⟩,
    rw [←group.mul_right_cancel_iff n⁻¹,
        group.mul_assoc, group.mul_assoc, group.mul_assoc] at hm₁,
    suffices : g * n * g⁻¹ = m * n⁻¹, 
      rw this, exact K.mul_mem hm₀ (K.inv_mem hn),
    simp [←group.mul_assoc] at hm₁; assumption
  end, .. K }

end subgroup

end mygroup
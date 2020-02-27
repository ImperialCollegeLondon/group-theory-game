import group.theorems -- basic interface for groups
import group.group_powers

/-!

Basic definitions for subgroups in group theory.
Not for the mathematician beginner. 

-/

-- We're always overwriting group theory here so we always work in
-- a namespace
namespace mygroup

/- subgroups (bundled) -/

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

-- we put dashes in all the names, because we'll define
-- non-dashed versions which don't mention `carrier` at all
-- and just talk about elements of the subgroup.

namespace subgroup

variables {G : Type} [group G] (H : subgroup G)

-- a subgroup can be thought of as a subset.
-- Let's not use this for now.
-- instance : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

-- Instead let's define ∈ directly
instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

-- subgroups form a lattice and we might want to prove this
-- later on?
instance : has_le (subgroup G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup G} (h : H.carrier = K.carrier) : H = K :=
by cases H; cases K; congr'

/-- Two subgroups are equal if they have the same elements. -/
theorem ext {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := ext' $ set.ext h

lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {H K : subgroup G} :
  H.carrier = K.carrier ↔ H = K :=
⟨ext', λ h, h ▸ rfl⟩

attribute [ext] subgroup.ext

/-- A subgroup contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup.mul_mem' _

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := subgroup.inv_mem' _ 

-- Defintion of normal subgroup
class normal {G : Type} [group G] (K : subgroup G) :=
(conjugate : ∀ g : G, ∀ k ∈ K, (g * k * g⁻¹) ∈ K)

-- Central subgroup
class central {G : Type} [group G] (K : subgroup G) :=
(comm : ∀ g : G, ∀ k ∈ K, k * g = g * k)

end subgroup

end mygroup
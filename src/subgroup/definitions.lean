import group.theorems -- basic interface for groups
import group_theory.group_action

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

-- Defintion of normal subgroup (in a bundled form)
structure normal (G : Type) [group G] extends subgroup G :=
(conj_mem' : ∀ n, n ∈ carrier → ∀ g : G, g * n * g⁻¹ ∈ carrier)

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

-- Coersion to group
-- Coercion from subgroup to underlying type -/

instance : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

lemma mem_coe' {g : G} : g ∈ (H : set G) ↔ g ∈ H := iff.rfl

instance (K : subgroup G) : group ↥K :=
{ mul := λ a b, ⟨a.1 * b.1, K.mul_mem' a.2 b.2⟩,
  one := ⟨1, K.one_mem'⟩,
  inv := λ a, ⟨a⁻¹, K.inv_mem' a.2⟩,
  mul_assoc := λ a b c, by { cases a, cases b, cases c, refine subtype.ext _, 
    apply group.mul_assoc },
  one_mul := λ a, by { cases a, apply subtype.ext, apply group.one_mul },
  mul_left_inv := λ a, by { cases a, apply subtype.ext, 
    apply group.mul_left_inv } } 

-- This is so I can write K : subgroup G
instance normal_to_subgroup : has_coe (normal G) (subgroup G) := 
  ⟨λ K, K.to_subgroup⟩

-- This saves me from writting m ∈ (K : subgroup G) every time
instance normal_has_mem : has_mem G (normal G) := ⟨λ m K, m ∈ K.carrier⟩

instance normal_to_set : has_coe (normal G) (set G) := ⟨λ K, K.carrier⟩


-- Defining cosets thats used in some lemmas
def lcoset (g : G) (K : subgroup G) := {s : G | ∃ k ∈ K, s = g * k}
def rcoset (g : G) (K : subgroup G) := {s : G | ∃ k ∈ K, s = k * g}
notation g ` •• ` :70 H :70 := lcoset g H
notation H ` •• ` :70 g :70 := rcoset g H

attribute [reducible] lcoset rcoset

-- Defining the the center of a group is a subgroup
/- Should probably define it as a normal subgroup
def center (G : Type) [group G] : subgroup G :=
{ carrier  := {g : G | ∀ k : G, k * g = g * k},
  one_mem' := λ k, by simp,
  mul_mem' := λ x y hx hy k, by rw [←group.mul_assoc, hx, group.mul_assoc, hy, ←group.mul_assoc],
  inv_mem' := λ x hx k,
  begin
    apply group.mul_left_cancel x,
    iterate 2 {rw ←group.mul_assoc},
    rw [←hx, group.mul_right_inv, group.mul_assoc, group.mul_right_inv], simp
  end
} -/

end subgroup

namespace normal

variables {G : Type} [group G]

lemma conj_mem  (N : normal G) (n : G) (hn : n ∈ N) (g : G) :
  g * n * g⁻¹ ∈ N := N.conj_mem' n hn g

@[ext] lemma ext (A B : normal G) (h : ∀ g, g ∈ A ↔ g ∈ B) : A = B :=
begin
  cases A with A, cases B with B, cases A with A, cases B with B,
  suffices : A = B,
    simp * at *,
  ext x, exact h x
end

end normal

end mygroup

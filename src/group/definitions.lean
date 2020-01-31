import tactic
import algebra.pi_instances
-- for one lemma about finite products??
/-!

Basic definitions in group theory.
Not for the mathematician beginner. 

Source: 
https://xenaproject.wordpress.com/2018/04/30/group-theory-revision/

-/

set_option old_structure_cmd true -- it's better for this kind of stuff

-- We're always overwriting group theory here so we always work in
-- a namespace

namespace mygroup

-- groups

section groupdefs 

-- Set up notation typeclass using `extends`.
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

-- definition of the group structure
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

class comm_group (G : Type) extends group G :=
(mul_comm : ∀ a b : G, a * b = b * a)

end groupdefs

/- homomorphisms of groups -/

section group_homs

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
structure group_hom (G : Type) (H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →* `:25 := group_hom

-- coercion to a function
instance {M : Type*} {N : Type*} {mM : group M} {mN : group N} :
  has_coe_to_fun (M →* N) :=
⟨_, group_hom.to_fun⟩

end group_homs

-- can't open a namespace inside a section!
namespace group_hom

section group_homs

variables {G : Type} [group G] {H : Type} [group H]

/-- If f is a group homomorphism then f (a * b) = f a * f b. -/
@[simp]
lemma map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
f.map_mul' a b

end group_homs -- section

end group_hom -- namespace

/- subgroups (bundled) -/

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

namespace subgroup

section subgroups

variables {G : Type} [group G] (H : subgroup G)

instance : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

instance : has_le (subgroup G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

lemma mem_coe {g : G} : g ∈ (H : set G) ↔ g ∈ H := iff.rfl

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup G} (h : (H : set G) = K) : H = K :=
by cases H; cases K; congr'

/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {H K : subgroup G} : ((H : set G) = K) ↔ H = K :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two subgroups are equal if they have the same elements. -/
theorem ext {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := ext' $ set.ext h

attribute [ext] subgroup.ext

/-- A subgroup contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup.mul_mem' _

end subgroups

-- -- needs a local instance from my comm_groups to Lean's comm_monoids

-- /-- A finite product of elements of a submonoid of a commutative monoid is in the submonoid. -/
-- lemma prod_mem {G : Type} [comm_group G] (K : subgroup G)
--   {ι : Type*} [decidable_eq ι] {t : finset ι} {f : ι → G} :
--   (∀c ∈ t, f c ∈ K) → t.prod f ∈ K :=
-- finset.induction_on t (by simp [S.one_mem]) (by simp [S.mul_mem] {contextual := tt})


end subgroup

end mygroup
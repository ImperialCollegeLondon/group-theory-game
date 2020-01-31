import tactic
import subgroup.theorems

/-!

Group homomorphisms

Definition file -- not for beginner mathematicians
-/

-- We're always overwriting group theory here so we always work in
-- a namespace
namespace mygroup

/- homomorphisms of groups -/

/-- Bundled group homomorphisms -/
structure group_hom (G : Type) (H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

-- notation
infixr ` →* `:25 := group_hom

-- coercion to a function
instance {G H : Type} {hG : group G} {hH : group H} :
  has_coe_to_fun (G →* H) :=
⟨_, group_hom.to_fun⟩

namespace group_hom

variables {G : Type} [group G] {H : Type} [group H]

/-- If f is a group homomorphism then f (a * b) = f a * f b. -/
@[simp]
lemma map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
f.map_mul' a b

end group_hom -- namespace for group homs

end mygroup -- namespace for the project
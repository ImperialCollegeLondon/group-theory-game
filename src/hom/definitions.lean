import tactic
import subgroup.quotient

/-!

Group homomorphisms

Definition file -- not for beginner mathematicians
-/

-- We're always overwriting group theory here so we always work in
-- a namespace
namespace mygroup

/- homomorphisms of groups -/

/-- Bundled group homomorphisms -/
structure group_hom (G H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

-- notation
infixr ` →* `:25 := group_hom

-- coercion to a function
instance {G H : Type} [group G] [group H] :
  has_coe_to_fun (G →* H) := ⟨_, group_hom.to_fun⟩

/-- Group isomorphism as a bijective group homomorphism -/
structure group_iso (G H : Type) [group G] [group H] extends group_hom G H :=
(is_bijective : function.bijective to_fun)
notation G ` ≅ ` H := group_iso G H

-- Coercion from `group_iso` to `group_hom`
instance {G H : Type} [group G] [group H] : 
  has_coe_t (G ≅ H) (G →* H) := ⟨group_iso.to_group_hom⟩

instance coe_iso_to_fun {G H : Type} [group G] [group H] :
  has_coe_to_fun (G ≅ H) := ⟨_, group_iso.to_group_hom⟩

-- Should we define it this way or as an extension of equiv that preserves mul? 

/- Alternative definition
structure group_equiv (G H : Type) [group G] [group H] extends G ≃ H :=
(map_mul' : ∀ x y : G, to_fun (x * y) = to_fun x * to_fun y) 

notation G ` ≅ ` H := group_equiv G H

-- Coercion from `group_equiv` to `group_hom`
instance {G H : Type} [group G] [group H] : 
  has_coe (G ≅ H) (G →* H) := ⟨λ f, ⟨f.to_fun, f.map_mul'⟩⟩ -/

namespace group_hom

variables {G H K : Type} [group G] [group H] [group K]

/-- If f is a group homomorphism then f (a * b) = f a * f b. -/
@[simp]
lemma map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
f.map_mul' a b

/-- The composition of two group homomorphisms form a group homomorphism -/
def map_comp (f : G →* H) (g : H →* K) : G →* K := 
{ to_fun   := g ∘ f, 
  map_mul' := λ x y, by simp }
notation g ` ∘* ` f := map_comp f g

/-- The composition of two group isomorphisms form a group isomorphism -/
def iso_comp (f : G ≅ H) (g : H ≅ K) : G ≅ K := 
{ is_bijective := function.bijective.comp g.is_bijective f.is_bijective,
  .. (g : group_hom H K) ∘* (f : group_hom G H) }

end group_hom -- namespace for group homs

end mygroup -- namespace for the project
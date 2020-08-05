import group.theorems

-- In this file we define subgroups as a group with a injective homomorphism 

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

@[simp] lemma to_fun_eq_coe {G H : Type} [group G] [group H]
  (f : G →* H) : f.to_fun = f := rfl

-- the identity homomorphism
def id_hom {G : Type} [group G] : G →* G := ⟨id, λ x y, rfl⟩

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

@[simp] lemma coe_map_comp (f : G →* H) (g : H →* K) : ((g ∘* f) : G → K) =
  g ∘ f := rfl

/-- A group is isomorphic to itself by the identity homomorphism -/
def iso_refl : G ≅ G := 
{ is_bijective := function.bijective_id, .. id_hom }

/-- The composition of two group isomorphisms form a group isomorphism -/
def iso_comp (f : G ≅ H) (g : H ≅ K) : G ≅ K := 
{ is_bijective := function.bijective.comp g.is_bijective f.is_bijective,
  .. (g : group_hom H K) ∘* (f : group_hom G H) }

/-- An equiv between two groups that preserves multiplication forms an isomorphism -/
def iso_of_mul_equiv (f : G ≃* H) : G ≅ H := 
{ to_fun := f, map_mul' := f.map_mul',
  is_bijective := equiv.bijective f.to_equiv }

/-- An isomorphism between two groups from an mul_equiv -/
noncomputable def mul_equiv_of_iso (f : G ≅ H) : G ≃* H := 
{ map_mul' := map_mul f, .. equiv.of_bijective _ f.is_bijective }

/-- If the group `G` is isomorphic to the group `H`, then `H` is isomorphic to `G`-/
noncomputable def iso_symm (f : G ≅ H) : H ≅ G := 
  iso_of_mul_equiv $ mul_equiv.symm $ mul_equiv_of_iso f

end group_hom -- namespace for group homs

class subgroup_of (G : Type) [group G] (H : Type) [group H] := 
(to_hom : H →* G) (is_inj : function.injective to_hom)

namespace subgroup

-- First we will need to make this subgroups a complete lattice

variables {G : Type} (H K : Type) [group G] [group H] [group K]

instance : has_mul (H × K) := ⟨λ ⟨h₀, k₀⟩ ⟨h₁, k₁⟩, ⟨h₀ * h₁, k₀ * k₁⟩⟩

@[simp] lemma prod_mul (h₀ h₁ : H) (k₀ k₁ : K) : 
  (h₀, k₀) * (h₁, k₁) = (h₀ * h₁, k₀ * k₁) := rfl

instance : has_one (H × K) := ⟨⟨1, 1⟩⟩

@[simp] lemma prod_one_mul (h : H) (k : K) : 1 * (h, k) = (h, k) := sorry

instance : has_inv (H × K) := ⟨λ ⟨h, k⟩, ⟨h⁻¹, k⁻¹⟩⟩

instance : group (H × K) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := λ ⟨h₀, k₀⟩ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩, by simp [group.mul_assoc],
  one_mul := λ ⟨h, k⟩, by simp,
  mul_left_inv := sorry }




end subgroup

end mygroup -- namespace for the project
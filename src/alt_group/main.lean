import group.theorems

-- In this file we define subgroups as a group with a injective homomorphism 

namespace mygroup

open set

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

/-- If f is a group homomorphism then f 1 = 1. -/
@[simp] lemma map_one (f : G →* H) : f 1 = 1 :=
begin
  have h : f 1 * f 1 = f 1,
    rw ←f.map_mul,
    rw group.one_mul, 
  rwa group.mul_left_eq_self at h, 
end

/-- If f is a group homomorphism then f(x⁻¹) = f(x)⁻¹ -/
@[simp] lemma map_inv (f : G →* H) {x : G} : f (x⁻¹) = (f x)⁻¹ :=
begin
  apply group.eq_inv_of_mul_eq_one,
  rw ←f.map_mul,
  rw group.mul_left_inv,
  rw f.map_one,
end

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

variables {G : Type} [group G] {H K : Type} [group H] [group K] 
variables [subgroup_of G H] [subgroup_of G K]

/- 
instance : has_mul (H × K) := ⟨λ ⟨h₀, k₀⟩ ⟨h₁, k₁⟩, ⟨h₀ * h₁, k₀ * k₁⟩⟩

@[simp] lemma prod_mul (h₀ h₁ : H) (k₀ k₁ : K) : 
  (h₀, k₀) * (h₁, k₁) = (h₀ * h₁, k₀ * k₁) := rfl

instance : has_one (H × K) := ⟨(1, 1)⟩

@[simp] lemma prod_one_def : (1 : H × K) = (1, 1) := rfl

@[simp] lemma prod_one_mul (h : H) (k : K) : 1 * (h, k) = (h, k) := by simp
  
instance : has_inv (H × K) := ⟨λ ⟨h, k⟩, ⟨h⁻¹, k⁻¹⟩⟩

@[simp] lemma prod_inv_def (h : H) (k : K) : (h, k)⁻¹ = (h⁻¹, k⁻¹) := rfl

@[simp] lemma prod_mul_left_inv (h : H) (k : K) : (h, k)⁻¹ * (h, k) = 1 := by simp

instance : group (H × K) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := λ ⟨h₀, k₀⟩ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩, by simp [group.mul_assoc],
  one_mul := by simp,
  mul_left_inv := by simp }
-/

-- The intersection of two subgroups is the elements of G that get hit by both homomorphisms

inductive inter (G : Type) [group G] (H : Type) (K : Type) [group H] [group K] 
  [hH : subgroup_of G H] [hK : subgroup_of G K] : Type
| mk (g : G) : (g ∈ range hH.to_hom) → (g ∈ range hK.to_hom) → inter

open inter group_hom

instance : has_mul (inter G H K) := 
⟨ λ ⟨a, haH, haK⟩ ⟨b, hbH, hbK⟩, mk (a * b) 
  (by { rcases haH with ⟨h₀, rfl⟩, rcases hbH with ⟨h₁, rfl⟩,
    refine ⟨h₀ * h₁, map_mul _ _ _⟩ })
  (by { rcases haK with ⟨k₀, rfl⟩, rcases hbK with ⟨k₁, rfl⟩,
    refine ⟨k₀ * k₁, map_mul _ _ _⟩ }) ⟩

instance : has_one (inter G H K) := ⟨mk 1 ⟨1, map_one _⟩ ⟨1, map_one _⟩⟩

instance : has_inv (inter G H K) := 
⟨ λ ⟨a, haH, haK⟩, mk a⁻¹ 
  (by { rcases haH with ⟨h, rfl⟩, exact ⟨h⁻¹, map_inv _⟩ })
  (by { rcases haK with ⟨k, rfl⟩, exact ⟨k⁻¹, map_inv _⟩ }) ⟩

instance : group (inter G H K) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := 
    begin
      rintros ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩,
      show mk (a * b * c) _ _ = mk (a * (b * c)) _ _,
      simp [group.mul_assoc]
    end,
  one_mul := 
    begin
      rintro ⟨a, _⟩,
      show mk (1 * a) _ _ = _, simp
    end,
  mul_left_inv := 
    begin
      rintro ⟨a, _⟩,
      show mk (a⁻¹ * a) _ _ = _,
      simpa [group.mul_left_inv]
    end }

instance : subgroup_of G (inter G H K) := 
{ to_hom := ⟨λ ⟨g, _, _⟩, g, λ ⟨x, _, _⟩ ⟨y, _, _⟩, rfl⟩,
  is_inj := 
    begin
      rintros ⟨x, _, _⟩ ⟨y, _, _⟩ hxy,
      change x = y at hxy,
      simpa using hxy
    end }

-- def inf := 
-- def inf (φ : H →* G) (ψ : K →* G)

end subgroup

end mygroup
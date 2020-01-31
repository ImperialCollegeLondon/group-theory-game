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

-- Set up notation typeclass using `extends`.
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

-- definition of the group structure
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-- Bundled monoid homomorphisms; use this for bundled group homomorphisms too. -/
structure group_hom (G : Type) (H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infixr ` →* `:25 := group_hom

-- coercion to a function
instance {M : Type*} {N : Type*} {mM : group M} {mN : group N} :
  has_coe_to_fun (M →* N) :=
⟨_, group_hom.to_fun⟩

namespace group_hom

variables {G : Type} [group G] {H : Type} [group H]

/-- If f is a group homomorphism then f (a * b) = f a * f b. -/
@[simp]
lemma map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
f.map_mul' a b

end group_hom

end mygroup
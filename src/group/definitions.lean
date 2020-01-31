import tactic
/-!

Basic definitions in group theory.
The beginner mathematician should be looking in the files called
`theorems.lean` rather than these ones; the definitions are
rather more intimidating.

Source: 
https://xenaproject.wordpress.com/2018/04/30/group-theory-revision/

-/

set_option old_structure_cmd true -- it's better for this kind of stuff

-- We're overwriting inbuilt group theory here so we always work in
-- a namespace

namespace mygroup

-- definitions of the group classes

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

end mygroup
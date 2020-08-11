import finiteness.fintype2
import subgroup.theorems

-- in this file we get fintype2 working with groups. 
-- For example we prove that a subgroup of a finite group is finite.

-- finiteness of subgroups

-- We will prove that if G is a finite group and H is a subgroup
-- then the promotion of H to a group is also finite

-- remember : (H : subgroup G) -- H is a *term* not a type

namespace mygroup

variables (G : Type) [group G]

-- use fintype2 to say a group is finite

variable [fintype2 G]

variable (H : subgroup G)

instance : fintype2 H := fintype2.set H.carrier

example (G : Type) [group G] [fintype2 G] (H : subgroup G) : fintype2 H :=
by apply_instance

end mygroup


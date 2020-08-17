#exit

-- this was just a proof of concept

import finiteness.is_finite
import subgroup.theorems

-- in this file we get is_finite working with groups. 
-- For example we prove that a subgroup of a finite group is finite.

-- finiteness of subgroups

-- We will prove that if G is a finite group and H is a subgroup
-- then the promotion of H to a group is also finite

-- remember : (H : subgroup G) -- H is a *term* not a type

namespace mygroup

variables (G : Type) [group G]

-- use is_finite to say a group is finite

variable [is_finite G]

variable (H : subgroup G)

instance : is_finite H := is_finite.set H.carrier

example (G : Type) [group G] [is_finite G] (H : subgroup G) : is_finite H :=
by apply_instance

end mygroup


import group.basic

namespace mygroup

/-
 the type of group homs G → H is
 denoted f : G →* H
 and the underlying function of types is ⇑f : G → H
 TODO: can we switch those arrows off?
 the axiom:
`lemma group_hom.map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b`
-/

variables {G H : Type} [group G] [group H]

-- 

/-- If f is a group homomorphism then f 1 = 1. -/
@[simp]
lemma map_one (f : G →* H) : f 1 = 1 :=
begin
  apply 
end



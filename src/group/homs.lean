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

open group
-- 

/-- If f is a group homomorphism then f 1 = 1. -/
@[simp]
lemma map_one (f : G →* H) : f 1 = 1 :=
begin
  have h : f 1 * f 1 = f 1,
    rw ←f.map_mul,
    rw group.one_mul, -- annoying but stops cheating
  rw group.mul_left_eq_self at h, -- annoying
  assumption
end

end mygroup


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

namespace group_hom

variables {G H : Type} [group G] [group H]

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

/-- If f is a group homomorphism then f(x⁻¹) = f(x)⁻¹ -/
@[simp]
lemma map_inv (f : G →* H) {x : G} : f (x⁻¹) = (f x)⁻¹ :=
begin
  
end

end group_hom

end mygroup

#check mygroup.group_hom.map_one

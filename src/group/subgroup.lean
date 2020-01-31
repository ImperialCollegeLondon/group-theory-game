import group.hom

namespace mygroup

/-
 the type of group homs G → H is
 denoted f : G →* H
 and the underlying function of types is ⇑f : G → H
 TODO: can we switch those arrows off?
 the axiom:
`lemma group_hom.map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b`
-/

variables {G : Type} [group G] {H : Type} [group H]

/-- The kernel of a homomorphism is a subgroup -/
def kernel (f : G →* H) : subgroup G :=
{ -- the underlying subset is the g such that f(g)=1
  carrier := {g | f g = 1},
  -- We now need to prove the axioms
  one_mem' := begin
    show (1 : G) ∈ {g : G | f g = 1},
    rw set.mem_set_of_eq,
    rw f.map_one,
  end,
  mul_mem' := begin
    intros x y hx hy,
    rw set.mem_set_of_eq at hx hy ⊢,
    rw [f.map_mul, hy, hx, group.mul_one]
  end,
  inv_mem' := begin
    intros x hx,
    rw set.mem_set_of_eq at hx ⊢,
    rw f.map_inv,
    apply group.inv_eq_of_mul_eq_one,
    simp [hx],
  end }
end mygroup

/-
TODO: image is a subgroup, kernel is a normal subgroup
-/

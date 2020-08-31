import hom.theorems

namespace mygroup

open_locale classical

open mygroup mygroup.subgroup mygroup.group_hom function set

variables {G H : Type} [group G] [group H] {f : G →* H} 

def C_infty := ℤ

instance : has_le C_infty := { le := ((≤) : ℤ → ℤ → Prop) }

instance group_order : group C_infty := {
  mul := ((+) : ℤ → ℤ → ℤ), one := (0 : ℤ), inv := λ x, (- x : ℤ),
  mul_assoc := show ∀ x y z : ℤ, x + y + z = x + (y + z), by exact add_assoc,
  one_mul := show ∀ x, (0 : ℤ) + x = x, by exact zero_add,
  mul_left_inv := show ∀ x : ℤ, - x + x = 0, by exact neg_add_self }

def order_map (g : G) : C_infty →* G := 
{ to_fun := λ n, ⦃n⦄^g,
  map_mul' := λ x y, by rw ← group.pow_add; refl }

noncomputable def order (g : G) := let ker := kernel (order_map g) in 
  if h : ∃ o ∈ ker, ∀ k ∈ ker, o ≤ k then classical.some h else (0 : ℤ)

@[simp] lemma order_def (g : G) : order g =  
  if h : ∃ o ∈ kernel (order_map g), ∀ k ∈ kernel (order_map g), o ≤ k 
  then classical.some h else (0 : ℤ) := rfl

end mygroup
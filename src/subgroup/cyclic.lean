import hom.theorems

namespace mygroup

open_locale classical

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

variables {G H : Type} [group G] [group H] {f : G →* H} 

def C_infty := ℤ

instance : has_le C_infty := { le := ((≤) : ℤ → ℤ → Prop) }

instance : group C_infty := 
{ mul := ((+) : ℤ → ℤ → ℤ), one := (0 : ℤ), inv := λ x, (- x : ℤ),
  mul_assoc := show ∀ x y z : ℤ, x + y + z = x + (y + z), by exact add_assoc,
  one_mul := show ∀ x, (0 : ℤ) + x = x, by exact zero_add,
  mul_left_inv := show ∀ x : ℤ, - x + x = 0, by exact neg_add_self }

instance : comm_group C_infty := 
{ mul_comm := show ∀ x y : ℤ, x + y = y + x, by exact add_comm
  .. show group C_infty, by apply_instance }

lemma C_infty_mul_comm (x y : C_infty) : x * y = y * x := 
  comm_group.mul_comm x y

def order_map (g : G) : C_infty →* G := 
{ to_fun := λ n, ⦃n⦄^g,
  map_mul' := λ x y, by rw ← group.pow_add; refl }

noncomputable def order (g : G) := let ker := kernel (order_map g) in 
  if h : ∃ o ∈ ker, ∀ k ∈ ker, o ≤ k then classical.some h else (0 : ℤ)

@[simp] lemma order_def (g : G) : order g =  
  if h : ∃ o ∈ kernel (order_map g), ∀ k ∈ kernel (order_map g), o ≤ k 
  then classical.some h else (0 : ℤ) := rfl

def mod (k : ℤ) : normal C_infty := 
{ carrier := { m : ℤ | k ∣ m },
  one_mem' := dvd_zero k,
  mul_mem' := λ _ _ hx hy, dvd_add hx hy,
  inv_mem' := λ x hx, (dvd_neg k x).2 hx,
  conj_mem' := λ x hx n,
    by { change k ∣ x at hx, change k ∣ n + x - n, simp [hx] } }

def cyclic (k : ℤ) := C_infty /ₘ mod k

instance cyclic_group (k : ℤ) : group (cyclic k) := 
  by unfold cyclic; apply_instance

instance cyclic_comm_group (k : ℤ) : comm_group (cyclic k) := 
{ mul_comm := 
    begin
      intros x y,
      rcases exists_mk x with ⟨x, rfl⟩,
      rcases exists_mk y with ⟨y, rfl⟩,
      rw [coe_mul, C_infty_mul_comm, ← coe_mul]
    end,
  .. show group (cyclic k), by apply_instance }

end mygroup
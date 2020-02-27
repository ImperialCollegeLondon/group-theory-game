import group.theorems -- definition of a group and a comm_group

/-
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

and `comm_group G` has the extra axiom

`mul_comm : ∀ (x y : G), x * y = y * x`

You access these axioms with `group.mul_assoc`, `group.one_mul` etc.
-/

-- This entire project takes place in the mygroup namespace
namespace mygroup

/- Our goal is to prove the following theorems (in the order
  listed) :

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`
`eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹`
`mul_left_eq_self {a b : G} : a * b = b ↔ a = 1`
`eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹`
`inv_inv (a : G) : a ⁻¹ ⁻¹ = a`
`inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b`

and possibly more to come if we run into stuff we need.

We start with only `mul_assoc`, `one_mul` and `mul_left_inv`. 

mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)
one_mul : ∀ (a : G), 1 * a = a
mul_left_inv : ∀ (a : G), a⁻¹ * a = 1

-/
namespace group

variables {G : Type} [group G]  

/-
lemma mul_left_cancel (a x y : G) (Habac : a * x = a * y) : x = y := 
  calc x = 1 * x : by rw one_mul
    ...  = (a⁻¹ * a) * x : by rw mul_left_inv
    ...  = a⁻¹ * (a * x) : by rw mul_assoc
    ...  = a⁻¹ * (a * y) : by rw Habac
    ...  = (a⁻¹ * a) * y : by rw mul_assoc
    ...  = 1 * y : by rw mul_left_inv
    ...  = y : by rw one_mul

@[simp] lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw [←mul_assoc, mul_left_inv, one_mul, h]
end

@[simp] theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_left_cancel a⁻¹,
  rw [←mul_assoc, mul_left_inv, one_mul]
end


@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_left_cancel a⁻¹,
  rw [←mul_assoc, mul_left_inv, mul_one, one_mul]
end
-/

lemma eq_mul_inv_of_mul_eq_right {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  rw [←h, mul_assoc, mul_right_inv c, mul_one]
end

lemma eq_mul_inv_of_mul_eq_left {a b c : G} (h : a * c = b) : c = a⁻¹ * b :=
begin
  rw [←h, ←mul_assoc, mul_left_inv a, one_mul]
end

/-
@[simp] lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  split,
    intro h,
    from calc a = b * b⁻¹ : by apply eq_mul_inv_of_mul_eq_right h
           ...  = 1 : by rw mul_right_inv,
    intro h,
    rw [h, one_mul]
end
-/

@[simp] lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 :=
begin
  split,
    intro h,
    from calc b = a⁻¹ * a : by apply eq_mul_inv_of_mul_eq_left h
           ...  = 1 : by rw mul_left_inv,
    intro h,
    rw [h, mul_one]
end

/-
lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  rw [←one_mul b⁻¹, ←h, mul_assoc, mul_right_inv b, mul_one]
end

@[simp] lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  rw [mul_left_inv, mul_right_inv]
end

@[simp] lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  apply mul_left_cancel a,
  rw [h, mul_right_inv]
end
-/

lemma unique_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
calc e = e * 1 : by rw mul_one
  ...  = 1 : by rw h 1

lemma unique_inv {a b : G} (h : a * b = 1) : b = a⁻¹ :=
begin
  apply mul_left_cancel a,
  rw [h, mul_right_inv]
end

lemma mul_right_cancel (a x y : G) (Habac : x * a = y * a) : x = y := 
calc x = x * 1 : by rw mul_one
  ...  = x * (a * a⁻¹) : by rw mul_right_inv
  ...  = x * a * a⁻¹ : by rw mul_assoc
  ...  = y * a * a⁻¹ : by rw Habac
  ...  = y * (a * a⁻¹) : by rw mul_assoc
  ...  = y * 1 : by rw mul_right_inv
  ...  = y : by rw mul_one

@[simp] lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y :=
begin
  split,
    from mul_left_cancel a x y,
    intro hxy,
    rwa hxy
end

@[simp] lemma mul_right_cancel_iff (a x y : G) : x * a = y * a ↔ x = y :=
begin
  split,
    from mul_right_cancel a x y,
    intro hxy,
    rwa hxy
end

@[simp] lemma inv_mul_inv_inv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_right_cancel (a * b),
  rw [mul_left_inv, 
  ←mul_left_cancel_iff b,
  mul_assoc, ←mul_assoc,
  mul_right_inv,
  one_mul, mul_one,
  ←mul_assoc, mul_left_inv, one_mul]
end

example (y z : G) (h : ∀ x : G, x * x = 1) : y * z = z * y :=
begin
  replace h : ∀ x : G, x = x⁻¹ :=
    by {intro x, apply mul_left_cancel x, rw [h x, mul_right_inv]},
  suffices : z * y = z⁻¹ * y⁻¹,
    rw [this, h (y * z)], apply inv_mul_inv_inv,
  conv {to_lhs, rw [h z, h y]}
end

end group

end mygroup
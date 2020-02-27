import group.definitions -- definition of a group and a comm_group

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

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c := 
begin
  -- We want to prove b = c.
  -- the left hand side is 1 * b
  rw ←one_mul b,
  -- which is (a⁻¹ * a) * b
  rw ←mul_left_inv a,
  -- which is a⁻¹ * (a * b) by associativity
  rw mul_assoc,
  -- which is a⁻¹ * (a * c) by our hypothesis
  rw Habac,
  -- and now we do the same but bakwards
  rw [←mul_assoc, mul_left_inv, one_mul],
end

-- chance to use rwa
lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rwa [←mul_assoc, mul_left_inv, one_mul],
end



theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_left_inv,
end

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- new
lemma eq_inv_mul_iff_mul_eq {a x y : G} : x = a⁻¹ * y ↔ a * x = y :=
begin
  split,
    exact mul_eq_of_eq_inv_mul,
  intro h,
  apply mul_left_cancel a,
  rwa [←mul_assoc, mul_right_inv, one_mul],
end

-- new
lemma mul_right_cancel (a x y : G) (Habac : x * a = y * a) : x = y := 
begin
  apply_fun (λ t, t * a⁻¹) at Habac,
  rwa [mul_assoc, mul_assoc, mul_right_inv, mul_one, mul_one] at Habac,
end

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  apply mul_right_cancel c,
  rw h, simp [mul_assoc, mul_left_inv, mul_one],
end

--new
lemma eq_mul_inv_iff_mul_eq {a b c : G} : a = b * c⁻¹ ↔ a * c = b :=
begin
  split,
    intro h,
    apply mul_right_cancel c⁻¹,
    rw [mul_assoc, mul_right_inv, mul_one, h],
  exact eq_mul_inv_of_mul_eq,
end

--new
lemma eq_mul_of_inv_mul_eq {a x y : G} (h : a⁻¹ * x = y) : x = a * y :=
begin
  rw [←h, ←mul_assoc, mul_right_inv, one_mul]
end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  rw ←eq_mul_inv_iff_mul_eq,
  rw mul_right_inv,
end

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  rwa [←eq_mul_inv_iff_mul_eq, one_mul] at h,
end

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  apply mul_left_cancel a,
  rw [mul_right_inv, h]
end

lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  rw [mul_left_inv, mul_right_inv]
end

end group

end mygroup
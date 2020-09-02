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

lemma mul_left_cancel (a x y : G) (Habac : a * x = a * y) : x = y := 
begin
  sorry
end

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  sorry
end

theorem mul_one (a : G) : a * 1 = a :=
begin
  sorry
end

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  sorry
end

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  sorry
end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  sorry
end

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  sorry
end

lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a :=
begin
  sorry
end

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  sorry
end

end group

end mygroup
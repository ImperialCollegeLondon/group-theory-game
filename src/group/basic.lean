import tactic
import group.definitions

/-
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
-/

-- Don't want to conflict with group namespace
-- so absolutely everything goes on in a secret namespace

namespace mygroup

/-
   Lean 3.4.1 also uses `mul_one : ∀ (a : G), a * 1 = a`
   as an axiom for groups due to some uninteresting typeclass
   thing, but we can deduce it from the above axioms.

   We make a general API of theorems for `group`.
   Namely

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`

-/
namespace group

variables {G : Type} [group G]  

-- We prove left_mul_cancel for group

lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c := 
λ (a b c : G) (Habac : a * b = a * c), -- got to deduce b = c.
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- This is also a useful intermediate lemma

lemma mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y :=
begin
  intro h,
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  rw mul_left_inv,
  rw one_mul,
  assumption
end

-- could prove it in `calc` mode:

lemma mul_eq_of_eq_inv_mul' {a x y : G} (h :x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  exact calc
  a⁻¹ * (a * x) = a⁻¹ * a * x : by rw mul_assoc
  ...           = 1 * x       : by rw mul_left_inv
  ...           = x           : by rw one_mul
  ...           = a⁻¹ * y     : by rw h  
end

-- Alternatively, get the simplifier to do some of the work for us
attribute [simp] one_mul mul_left_inv

lemma mul_eq_of_eq_inv_mul'' {a x y : G} : x = a⁻¹ * y → a * x = y :=
λ h, mul_left_cancel a⁻¹ _ _ $ by rw ←mul_assoc; simp [h]

-- and then mul_one

-- nice short proof
theorem mul_one (a : G) : a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_left_inv,
  -- note no refl
end



-- calc example (longer than previous one)
theorem mul_one' : ∀ (a : G), a * 1 = a :=
begin
  intro a, -- goal is a * 1 = a
  apply mul_left_cancel a⁻¹, -- goal now a⁻¹ * (a * 1) = a⁻¹ * a
  exact calc a⁻¹ * (a * 1) = (a⁻¹ * a) * 1 : by rw mul_assoc
          ...               = 1 * 1         : by rw mul_left_inv
          ...               = 1             : by rw one_mul
          ...               = a⁻¹ * a       : by rw mul_left_inv
end

-- term mode proof
theorem mul_one'' (a : G) : a * 1 = a :=
mul_eq_of_eq_inv_mul $ by simp

-- it's also a good simp lemma
attribute [simp] mul_one

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- another good simp lemma
attribute [simp] mul_right_inv

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin

end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  split,
  { intro h,
    replace h := eq_mul_inv_of_mul_eq h,
    rw mul_right_inv at h,
    assumption
  },
  { intro h,
    rw h,
    rw one_mul
  }
end

end group

end mygroup
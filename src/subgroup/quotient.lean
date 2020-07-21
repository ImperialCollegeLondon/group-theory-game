import subgroup.theorems group_theory.congruence

namespace mygroup

namespace quotient

-- We will in this file define quotient groups using congruences

/- We define `group_con` as an extention of `con` which respects the inverse 
operation -/
structure group_con (G : Type) [group G] extends con G :=
(inv' : ∀ {x y}, r x y → r x⁻¹ y⁻¹)

-- A `group_con G` induces a group structure with its congruence classes

variables {G : Type} [group G]

-- We define a coercion from `group_con G` to `setoid G` 
instance has_coe_to_setoid : has_coe (group_con G) (setoid G) := 
  ⟨λ R, R.to_con.to_setoid⟩

/- Coercion from a `group_con G` to its underlying binary relation -/
instance : has_coe_to_fun (group_con G) := ⟨_, λ R, λ x y, R.r x y⟩

lemma mul {R : group_con G} {x₀ x₁ y₀ y₁ : G} : 
  R x₀ x₁ → R y₀ y₁ → R (x₀ * y₀) (x₁ * y₁) := by apply R.mul'

lemma inv {R : group_con G} {x y : G} : R x y → R x⁻¹ y⁻¹ := by apply R.inv'

-- A quotient on a `group_con G` is the quotient on its coerced setoid
def quotient (R : group_con G) := quotient (R : setoid G)

variables {R : group_con G}

-- Coercion from a group to its quotient
instance : has_coe_t G (quotient R) := ⟨quotient.mk'⟩

-- We can think of the coercion above as making a term of `G` into its 
-- equivalence class. So two elements of type `quotient R` are equal iff 
-- they are related by the binary relation `R`
lemma eq {x y : G} : (x  : quotient R) = y ↔ R x y := quotient.eq'

def lift_on {β} {R : group_con G} (x : quotient R) (f : G → β) 
  (h : ∀ x y, R x y → f x = f y) : β := quotient.lift_on' x f h

def lift_on₂ {β} {R : group_con G} (x y : quotient R) (f : G → G → β)
  (h : ∀ a₁ a₂ b₁ b₂, R a₁ b₁ → R a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β := 
quotient.lift_on₂' x y f h

-- Mathematically, we define mul for `quotient R` by taking to congruence 
-- classes and outputing the congruence class of their mul, i.e. 
-- (*) : (⟦g⟧, ⟦h⟧) ↦ ⟦g * h⟧

-- In Lean, we achieve this by using `lift_on₂` where given some type `β` 
-- (in this case `quotient R`), two elements of `quotient R` and a function 
-- `f : G → G → β` that respects `R`, it returns a term of `β`.
instance : has_mul (quotient R) := 
{ mul := λ x y, lift_on₂ x y (λ x y , ((x * y : G) : quotient R)) 
    $ λ _ _ _ _ h₁ h₂, eq.2 (mul h₁ h₂) }

-- Similar story for the inverse in which we use `lift_on` instead.
-- Mathematically, the inverse is defined to be the congruence class of the 
-- inverse, i.e. (⁻¹) : ⟦g⟧ ↦ ⟦g⁻¹⟧
instance : has_inv (quotient R) := 
  ⟨λ x, lift_on x (λ x, ((x⁻¹ : G) : quotient R)) $ λ _ _ h, eq.2 (inv h)⟩

instance : has_one (quotient R) := ⟨((1 : G) : quotient R)⟩

-- We now simply need to prove all the group axioms

lemma mul_assoc' {a b c : quotient R} : a * b * c = a * (b * c) := sorry

lemma one_mul' {a : quotient R} : 1 * a = a := sorry

lemma mul_left_inv' {a : quotient R} : a⁻¹ * a = 1 := sorry

instance : group (quotient R) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := λ _ _ _, mul_assoc',
  one_mul := λ _, one_mul',
  mul_left_inv := λ _, mul_left_inv' }

end quotient

end mygroup
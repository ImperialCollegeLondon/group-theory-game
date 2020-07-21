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

lemma coe     (x : G)   : quotient.mk' x = (x : quotient R) := rfl 
lemma coe_mul (x y : G) : (x : quotient R) * y = ((x * y : G) : quotient R) := rfl  
lemma coe_inv (x : G)   : (x : quotient R)⁻¹ = ((x⁻¹ : G ): quotient R) := rfl
lemma coe_one           : 1 = ((1 : G) : quotient R) := rfl

-- I think the rhs is more desirable in most cases so I will make simp use them
attribute [simp] coe coe_mul coe_inv coe_one

-- We now simply need to prove all the group axioms

-- To prove propositions regarding elements of `quotient R` we need to use the 
-- induction principle for quotients `quotient.induciton_on`. 
-- In this case we are using the variant of this induction principle with 
-- three arguments.
-- Essentially, to prove a proposition true for all `x : quotient R`, it 
-- suffices to prove that the proposition is true for all `(g : G) : quotient R`
lemma mul_assoc' {a b c : quotient R} : a * b * c = a * (b * c) := 
begin
  apply quotient.induction_on₃' a b c,
  intros _ _ _, 
  iterate 3 { rw coe },
  iterate 4 { rw coe_mul },
  rw group.mul_assoc
end

lemma one_mul' {a : quotient R} : 1 * a = a := 
begin
  apply quotient.induction_on' a,
  intro x, rw [coe, coe_one, coe_mul, group.one_mul]  
end

lemma mul_left_inv' {a : quotient R} : a⁻¹ * a = 1 := 
begin
  apply quotient.induction_on' a,
  intro x, rw [coe, coe_inv, coe_mul, group.mul_left_inv, coe_one]
end

-- With that we find `quotient R` form a group
instance : group (quotient R) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := λ _ _ _, mul_assoc',
  one_mul := λ _, one_mul',
  mul_left_inv := λ _, mul_left_inv' }

-- But this is not how most of us learnt quotient groups. For us, quotient groups 
-- are defined by creating a group structure on the set of coests of a normal 
-- subgroup. We will show that these two definitions are, in fact, the same.

/- The main proposition we will prove is that given a subgroup H of the group G, 
the equivalence relation ~ : (g, k) ↦ g H = k H on G is a group congruence if 
and only if H is normal. -/

open mygroup.subgroup

variables {H : subgroup G} 

-- We will redeclare the notation since importing group_theory.congruence also 
-- imported some other notations using `•`
notation g ` • ` :70 H :70 := lcoset g H
notation H ` • ` :70 g :70 := rcoset g H

def lcoset_rel (H : subgroup G) := λ x y, x • H = y • H 
local notation x ` ~ ` y := lcoset_rel H x y

def lcoset_iseqv (H : subgroup G) : equivalence (lcoset_rel H) := 
begin
  refine ⟨by tauto, λ _ _ hxy, hxy.symm, _⟩,
  intros _ _ _ hxy hyz, unfold lcoset_rel at *, rw [hxy, hyz]
end 

def lcoset_setoid (H : subgroup G) : setoid G :=
{ r := lcoset_rel H,
  iseqv := lcoset_iseqv H}

/-- If `lcoset_rel H` is a congruence then `H` is normal -/
def normal_of_con 
  (hmul : ∀ x₀ x₁ y₀ y₁ : G, x₀ ~ x₁ → y₀ ~ y₁ → x₀ * y₀ ~ x₁ * y₁) 
  (hinv : ∀ x y : G, x ~ y → x⁻¹ ~ y⁻¹) : normal G := sorry

end quotient

end mygroup
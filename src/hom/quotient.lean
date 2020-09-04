import hom.basic group_theory.congruence

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
lemma coe_one           : ((1 : G) : quotient R) = 1 := rfl

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
  intro x, rw [coe, ←coe_one, coe_mul, group.one_mul]  
end

lemma mul_left_inv' {a : quotient R} : a⁻¹ * a = 1 := 
begin
  apply quotient.induction_on' a,
  intro x, rw [coe, coe_inv, coe_mul, group.mul_left_inv, coe_one]
end

-- With that we find `quotient R` form a group
instance of_quotient : group (quotient R) := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := λ _ _ _, mul_assoc',
  one_mul := λ _, one_mul',
  mul_left_inv := λ _, mul_left_inv' }

-- But this is not how most of us learnt quotient groups. For us, quotient groups 
-- are defined by creating a group structure on the set of coests of a normal 
-- subgroup. We will show that the equivalence relation `lcoset_rel H` in which 
-- `x ~ y ↔ x ⋆ H = y ⋆ H` is a group congruence if and only if H is normal.

/- The main proposition we will prove is that given a subgroup H of the group G, 
the equivalence relation ~ : (g, k) ↦ g H = k H on G is a group congruence if 
and only if H is normal. -/

open mygroup.subgroup lagrange function

variables {H : subgroup G} {N : normal G}

def lcoset_rel (H : subgroup G) := λ x y, x ⋆ H = y ⋆ H
local notation x ` ~ `:70 y := lcoset_rel H x y 
local notation x ` ~[ `:70 H:70 ` ] `:0 y:0 := lcoset_rel H x y

/-
infixr ` →ₗ `:25 := linear_map _
notation M ` →ₗ[`:25 R:25 `] `:0 M₂:0 := linear_map R M M₂
-/

lemma lcoset_rel_def (x y : G) : x ~ y ↔ x ⋆ H = y ⋆ H := iff.rfl

lemma lcoset_iseqv (H : subgroup G) : equivalence (lcoset_rel H) := 
begin
  refine ⟨by tauto, λ _ _ hxy, hxy.symm, _⟩,
  intros _ _ _ hxy hyz, unfold lcoset_rel at *, rw [hxy, hyz]
end 

lemma lcoset_mul {x₀ x₁ y₀ y₁ : G} 
  (hx : x₀ ~[↑N] x₁) (hy : y₀ ~[↑N] y₁) : (x₀ * y₀) ~[↑N] (x₁ * y₁) := 
begin
  rw [lcoset_rel_def, lcoset_eq] at *,
  have := N.conj_mem _ hx y₁⁻¹, 
  rw group.inv_inv at this,
  replace this := N.mul_mem' this hy,
  rw [←group.mul_assoc, group.mul_assoc (y₁⁻¹ * (x₁⁻¹ * x₀)), 
      group.mul_right_inv, group.mul_one, ←group.mul_assoc] at this,
  rwa [group.inv_mul, ←group.mul_assoc],
end

lemma lcoset_inv {x y : G} (hxy : x ~[↑N] y) : (x⁻¹ ~[↑N] y⁻¹) := 
begin
  rw [lcoset_rel_def, lcoset_eq] at *,
  rw ←group.inv_mul,
  apply N.inv_mem',
  convert N.conj_mem' _ hxy y,
  simp [←group.mul_assoc]
end

/-- If `H` is normal, then `lcoset_rel H` is a group congruence -/
def con_of_normal (G : Type) [group G] (N : normal G) : group_con G :=
{ r := lcoset_rel N,
  iseqv := lcoset_iseqv N, 
  mul' := λ x₀ x₁ y₀ y₁ hx hy, lcoset_mul hx hy,
  inv' := λ x y hxy, lcoset_inv hxy }

lemma con_of_normal_def {G : Type} [group G] {N : normal G} (x y : G) : 
con_of_normal G N x y ↔ x ~[↑N] y := iff.rfl

lemma con_one_of_mem : ∀ h ∈ H, h ~ 1 :=
begin
  intros h hh,
  rw [lcoset_rel_def, lcoset_eq], simpa  
end

lemma mem_of_con_one {g : G} (hg : g ~ 1) : g ∈ H :=
by rwa [lcoset_rel_def, lcoset_eq, group.one_inv, group.one_mul] at hg

/-- If `lcoset_rel H` is a congruence then `H` is normal -/
def normal_of_con (H : subgroup G) {R : group_con G} 
  (hR : R.r = lcoset_rel H) : normal G := 
{ conj_mem' := λ n hn g, mem_of_con_one $
    begin
      rw [←hR, (show (1 : G) = g * 1 * g⁻¹, by simp)],
      refine R.mul' (R.mul' (R.iseqv.1 _) _) (R.iseqv.1 _),
       { rw hR, exact con_one_of_mem _ hn }
    end .. H }

lemma con_one_iff_mem (h : G) : h ~ 1 ↔ h ∈ H := ⟨mem_of_con_one, con_one_of_mem h⟩

-- So now, whenever we would like to work with "normal" quotient groups of 
-- a group `G` over a normal group `N`, we write `quotient (con_of_normal N)`
notation G ` /ₘ `:70 N:70 := quotient (con_of_normal G N)

/-- For all elements `c : G /ₘ N`, there is some `g : G` such that `⟦g⟧ = c`-/
lemma exists_mk {N : normal G} (c : G /ₘ N) : ∃ g : G, (g : G /ₘ N) = c := 
  @quotient.exists_rep G (con_of_normal G N) c

/-- `(⟦p⟧ : G /ₘ N) = ⟦q⟧` iff `p ⋆ N = q ⋆ N` where `p q : G` -/
lemma mk_eq {p q : G} : (p : G /ₘ N) = q ↔ p ⋆ N = q ⋆ N :=
  ⟨λ h, quotient.eq.1 h, λ h, quotient.eq.2 h⟩

lemma mk_eq' {p q : G} : (p : G /ₘ N) = q ↔ q⁻¹ * p ∈ N :=
begin
  rw mk_eq,
  exact lcoset_eq
end

end quotient

end mygroup
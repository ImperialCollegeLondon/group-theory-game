import tactic

/-!

Basic definitions in group theory.

Source: 
https://xenaproject.wordpress.com/2018/04/30/group-theory-revision/

-/

set_option old_structure_cmd true -- it's better for this kind of stuff

-- We're overwriting inbuilt group theory here so we always work in
-- a namespace

namespace mygroup

-- definitions of the group classes

section groupdefs 

-- Set up notation typeclass using `extends`.
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

-- definition of the group structure
class group (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

class comm_group (G : Type) extends group G :=
(mul_comm : ∀ a b : G, a * b = b * a)

-- an example
instance perm_group (α : Type) : group (α ≃ α) :=
{ mul := function.swap equiv.trans,
  one := equiv.refl _,
  inv := equiv.symm,
  mul_assoc := by intros; ext; refl,
  one_mul := by intros; ext; refl,
  mul_left_inv := by intros; ext; simp }

end groupdefs

/- Our first task is to prove `mul_one` and `mul_right_inv`.
   We prove some other things along the way too -- we make 
   what a computer scientist would call "an interface for
   the group class".

  Examples of what we prove:

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`

-/
namespace group

variables {G : Type} [group G]  

-- We prove left_mul_cancel for group using `calc`.

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c := 
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

-- We can do all this one go:

lemma mul_left_cancel' (a b c : G) (Habac : a * b = a * c) : b = c := 
begin 
  rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac,
      ←mul_assoc, mul_left_inv, one_mul],
end

-- Because the above proof just uses one tactic, we could use `by`
-- instead of `begin ... end`:

lemma mul_left_cancel'' (a b c : G) (Habac : a * b = a * c) : b = c := 
by rw [←one_mul b, ←mul_left_inv a, mul_assoc, Habac,
  ←mul_assoc, mul_left_inv, one_mul]

-- The below is also a useful intermediate lemma

lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  rw mul_left_inv,
  rwa one_mul, -- rewrite then assumption
end

-- could prove it in `calc` mode:

lemma mul_eq_of_eq_inv_mul' {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  exact calc
  a⁻¹ * (a * x) = a⁻¹ * a * x : by rw mul_assoc
  ...           = 1 * x       : by rw mul_left_inv
  ...           = x           : by rw one_mul
  ...           = a⁻¹ * y     : by rw h  
end

attribute [simp] one_mul mul_left_inv

-- Alternatively, get the simplifier to do some of the work for us
lemma mul_eq_of_eq_inv_mul'' {a x y : G} : x = a⁻¹ * y → a * x = y :=
λ h, mul_left_cancel a⁻¹ _ _ $ by rw ←mul_assoc; simp [h]

-- We can now prove `mul_one`:

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

-- mul_left_inv is an axiom: here's mul_right_inv. 

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- another good simp lemma
attribute [simp] mul_right_inv

-- We already proved `mul_eq_of_eq_inv_mul` but there are several other
-- similar-looking, but slightly different, versions of this. Here
-- is one.
lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  rw ←h,
  rw mul_assoc,
  rw mul_right_inv,
  rw mul_one
end

-- one-liner proof
lemma eq_mul_inv_of_mul_eq' {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
by rw [←h, mul_assoc, mul_right_inv, mul_one]

-- proof using automation
lemma eq_mul_inv_of_mul_eq'' {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
by simp [h.symm, mul_assoc]

lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c :=
begin
  rw [←h, ←mul_assoc, mul_left_inv b, one_mul]
end

-- Another useful lemma for the interface:
lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  split,
  { intro h,
    replace h := eq_mul_inv_of_mul_eq h,
    rw mul_right_inv at h,
    assumption },
  { intro h,
    rw h,
    rw one_mul }
end

lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 :=
begin
  split,
    intro h,
    from calc b = a⁻¹ * a : by apply eq_inv_mul_of_mul_eq h
           ...  = 1 : by rw mul_left_inv,
    intro h,
    rw [h, mul_one]
end

-- Another useful lemma for the interface.
-- Note use of the powerful `convert` tactic.
-- `eq_mul_inv_of_mul_eq h` says ` a = 1 * b⁻¹` which is
-- equal to our goal; convert creates the goals necessary
-- to prove this
lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  convert eq_mul_inv_of_mul_eq h,
  rw one_mul, -- `simp` would also work
end

-- Another useful lemma for the interface
lemma inv_inv (a : G) : a ⁻¹ ⁻¹ = a :=
begin
  symmetry,
  apply eq_inv_of_mul_eq_one,
  simp,
end

-- Another useful lemma for the interface
lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  -- we can change hypotheses with the `replace` tactic.
  -- h implies a = 1 * b⁻¹
  replace h := eq_mul_inv_of_mul_eq h,
  -- and so a = b⁻¹
  rw one_mul at h,
  -- By substituting in, we have to prove (b⁻¹)⁻¹ = b
  rw h,
  -- and we just did this, it's `inv_inv`
  rw inv_inv,
end

lemma unique_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
calc e = e * 1 : by rw mul_one
  ...  = 1 : by rw h 1

-- Maybe add unique_id but with x * e = x

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

lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y :=
begin
  split,
    from mul_left_cancel a x y,
    intro hxy,
    rwa hxy
end

lemma mul_right_cancel_iff (a x y : G) : x * a = y * a ↔ x = y :=
begin
  split,
    from mul_right_cancel a x y,
    intro hxy,
    rwa hxy
end

@[simp] lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
begin
  rw ←mul_assoc, simp
end

@[simp] lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  simp
end

lemma inv_mul (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv, simp [mul_assoc]
end

lemma one_inv : (1 : G)⁻¹ = 1 :=
by conv_rhs { rw [←(mul_left_inv (1 : G)), mul_one] }

attribute [simp] mul_left_cancel_iff mul_right_cancel_iff inv_mul inv_inv  one_inv

@[simp] theorem inv_inj_iff {a b : G}: a⁻¹ = b⁻¹ ↔ a = b :=
begin
  split,
  { intro h,
    rw [← inv_inv a, h, inv_inv b] },
  { rintro rfl,
    refl }  
end   

theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a :=
begin
  split;
  { rintro rfl,
    rw inv_inv }
end  

-- **TODO** is this a good simp lemma? I don't think RHS is
-- strictly simpler than LHS.
@[simp] theorem mul_comm {G : Type} [comm_group G] (g h : G) : 
  g * h = h * g := comm_group.mul_comm g h

-- **TODO** open an issue about abel only working with `*`. We
-- have `group` working but not `comm_group`. It
-- would be an interesting exercise to get `abel` working.

end group

end mygroup
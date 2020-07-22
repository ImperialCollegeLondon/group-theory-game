-- Iteration of equivalences over the integers

-- Idea -- if f is a bijection then we can talk about f^n for n an integer,
-- because f⁻¹ is just the inverse bijection

import tactic

namespace int


-- Giulia I can't see the chat. @me if you have a question.
-- Oh great I can hear you!
-- Sorry, my family are around

-- First we define f^n as a function
-- This is the n'th iterate of f as a function from X to X
--def iterate {X : Type} (n : ℤ) (h : X ≃ X) : X ≃ X :=
--h^n

-- honest approach via iterations needs big API before
-- you can make ℤ → ≃ → ≃


-- there is already the notation `f^[n]` when f is a function and
-- n is a natural. I will steal their binding power.

-- _ `^[`:1 _:1 `]`:0 := nat.iterate #1 #0

-- here is some cool notation (hopefully with the correct binding power)

def iterate {X : Type} (n : ℤ) (f : X ≃ X) : X ≃ X := f^n

-- make a definition for iterate
-- Not sure what we need

-- currently: no interface at all for `iterate`. 

-- I mean that there are functions in the iterate namespace.
-- For example 

-- notation might have to be changed but all I care about is
-- that n must be to left of f. No arguments until it
-- turns out rubbish
--notation `⦃`:1 n `⦄^`:1 f := int.iterate n f

namespace iterate

variables {X : Type} (m n : ℤ) (f : X ≃ X) (x : X)
--
lemma comp : int.iterate m f (int.iterate n f x) = int.iterate (m + n) f x :=
begin
  suffices : (f^m * f^n) x = (f^(m+n)) x,
    convert this,
  rw gpow_add,
end


lemma foo (G : Type) [group G] (g : G) (a : ℤ) : g ^ -a = g⁻¹ ^ a :=
by group

@[simp] lemma zero : iterate 0 f = equiv.refl X := rfl
@[simp] lemma one : iterate 1 f = f := by {ext x, refl}
@[simp] lemma neg_one : iterate (-1) f = f.symm := by {ext x, refl}--funext $ λ x, --funext $ λ x, rfl -- :-)

lemma neg (a : ℤ) : iterate (-a) f = iterate a f.symm :=
begin
  show f^(-a) = f⁻¹^a,
  group
end


lemma succ : int.iterate n f (f x) = int.iterate (n + 1) f x := 
comp n 1 f x

theorem mul (f : X ≃ X) (a b : ℤ) (x : X) : int.iterate a (int.iterate b f) = 
int.iterate (a * b) f
:=
begin
  show (f^b)^a = f^(a*b),
  group,
end


-- int.iterate n (lmul g) 1 * h = int.iterate n (lmul g) h, 


#exit

-- could be dead code. Is it more fun to make the API or to steal it?

-- qould it be fun to make the API for this, building up to iterate
-- or would it be boring? It could be an "extra level".
def iterate_aux {X : Type} (h : X ≃ X) : ℤ → X → X
| (of_nat n) := h^[n]
| (neg_succ_of_nat n) := h.symm^[n+1]

notation f`^⦃`:1 n`⦄`:1 := int.iterate_aux f n

variable {X : Type}

namespace iterate_aux

-- our first piece of API!
@[simp] theorem zero (f : X ≃ X) (x : X) : f^⦃0⦄ x = x := rfl

-- here's the problem we ran into:
-- if we can prove these two goals we've int.iterate'
-- ⊢ f^⦃-n⦄ (f^⦃n⦄ a) = a
-- ⊢ f^⦃n⦄ (f^⦃-n⦄ a) = a

-- important theorem which we can use to solve both of these goals.


-- **TODO** -- ask on Zulip if we can put f^⦃(a+b)⦄ or even better f^⦃a+b⦄
theorem comp (f : X ≃ X) (a b : ℤ) (x : X) : f^⦃a⦄ (f^⦃b⦄ x) = 
(f^⦃a+b⦄ x) :=
begin
  sorry
end

-- How are we going to prove these?
-- Think of one theorem that would omply both results.
-- a theorem just about `f^⦃n⦄`. 
-- what more general theorem should we prove?
-- ⊢ f^⦃-n⦄ = inverse function to f^⦃n⦄

end iterate_aux

section deff
open iterate_aux

-- Now we try to define f^n as another bijection.
-- Note that `X ≃ X` is the type of bijections from `X` to `X`.
-- We also carry around the inverse function explicitly, rather
-- than just a proof that it exists, but this is an implementation
-- detail.
-- this is our goal -- to make this definition sorry-free
-- The goal: "we can iterate a bijection and get a bijection"
def iterate' {X : Type} (n : ℤ) (f : X ≃ X) : X ≃ X :=
{ to_fun := f^⦃n⦄,
  inv_fun := f^⦃-n⦄,
  left_inv := begin
    -- what is the goal?
    -- i have to prove something is a left inverse
    -- intro sometimes works
    intro x,
    simp [comp],
    -- earlier thoughts
    -- Two steps.
    -- We can prove `f^⦃0⦄ x = x`; the proof is `zero f x`
    -- (1) `n+n=0` (`ring` will prove this) 

    -- (2) f^⦃0⦄ x = x (part of the API already! It's `zero f x`)
    -- You now want to prove that f^⦃0⦄ x = x
    -- and deduce the result
  end,
  right_inv := λ a, by simp [comp]
}

end deff

namespace iterate'

-- -- lemma pow: need to prove this but we can't define the
-- lemma foo (f : X ≃ X) (a b : ℤ) : iterate' a (iterate' b f) =
-- iterate' (a * b) f :=
-- begin
--   simp [iterate'],
--   -- we're not ready for this 
--   sorry
-- end

-- I wrote this file once before. I'm going through it again.
-- I'm going to make a basic interface for the int.iterate function
-- sending `f : X ≃ X` and `n : ℤ` to `f^⦃n⦄ : X → X` and also the
-- on sending it to `int.iterate' n f : X ≃ X`

-- Story so far: we've defined `f^⦃n⦄` and it worked fine
-- Now we need to build the proof that `f^⦃-n⦄` is the inverse bijection¬

variables {X} (h : X ≃ X)
#exit

--example (a b : ℕ) : h^[a+b] = (h^[a]) ∘ (h^[b]) := sorry -- brackets needed

@[simp] lemma zero : h^⦃0⦄ = id := rfl
@[simp] lemma one : h^⦃1⦄ = h := by funext; refl  --rfl --funext $ λ x, rfl
@[simp] lemma neg_one : h^⦃-1⦄ = h.symm := funext $ λ x, rfl -- :-)

lemma neg (a : ℤ) : h^⦃-a⦄ = h.symm^⦃a⦄ :=
begin
  cases a,
  cases a,
  ext, refl,
  ext, refl,
  ext, refl,
end

example (i : ℕ) : -[1+ i] = -((i : ℤ) + 1) := by exact neg_succ_of_nat_eq i

lemma add_one (a : ℤ) : h^⦃a+1⦄ = h^⦃a⦄ ∘ h :=
begin
  cases a with i i,
  { refl},
  { suffices :  h^⦃(-↑i)⦄ = h^⦃-(i + 1)⦄ ∘ h,
      convert this, rw neg_succ_of_nat_eq, ring,
    rw neg,
    rw neg,
    ext,
    norm_cast,
    have : h.symm^⦃↑i⦄ ∘ h.symm = h.symm^⦃↑(i + 1)⦄,
      refl,
    rw ←this,
    simp},
end

lemma sub_one (a : ℤ) : h^⦃a-1⦄ = h^⦃a⦄ ∘ h.symm :=
begin
  rw ←neg_one,
  rw ←h.symm_symm,
  rw ←neg,
  rw (show -(a-1)=-a+1, by ring),
  rw add_one,
  simp [neg],
end


lemma add (a b : ℤ) : h^⦃a + b⦄ = h^⦃a⦄ ∘ h^⦃b⦄ :=
begin
  apply int.induction_on b,
  {simp},
  { intro i,
    intro useful,
    rw ←add_assoc,
    rw add_one,
    rw useful,
    rw add_one,
  },
  { intro i,
    intro useful,
    rw ←add_sub_assoc,
    rw sub_one,
    rw useful,
    rw sub_one,
  },
end

end int.iterate

-- def pow_hom (g : G) (a b : ℕ) : pow g a * pow g b = pow g (a + b) :=
-- begin

--   sorry
-- end

-- /-- definition of map sending g, n to gⁿ , n ∈ ℤ -/
-- def zpow (g : G) : ℤ → G
-- | (of_nat n) := pow g n
-- | (neg_succ_of_nat n) := pow g⁻¹ (n+1)

--example (g : G) : G ≃ G := by suggest

def thing (g : G) : G ≃ G :=
{ to_fun := (* g),
  inv_fun := (* g⁻¹),
  left_inv := by intro x; simp,
  right_inv := by intro x; simp }

  open int.iterate

lemma foo (g j : G) (a : ℤ) : j * (thing g^⦃a⦄ 1) = thing g^⦃a⦄ j :=
begin
  revert j,
  apply int.induction_on a,
  { simp},
  { intro i,
    intro hi,
    intro j,
    rw int.iterate.add_one,
    unfold function.comp,
    rw ←hi (thing _ j),
    rw ←hi,
    unfold thing, simp [mygroup.group.mul_assoc],
  },
  { intro i,
    intro hi,
    intro j,
    rw int.iterate.sub_one,
    unfold function.comp,
    conv_rhs begin
      rw ←hi,
    end,
    rw ←hi,
    unfold thing, simp [mygroup.group.mul_assoc],
  }
end

def zpow' (g : G) : ℤ → G := λ z, (thing g)^⦃z⦄ 1

instance : has_pow G ℤ := ⟨zpow'⟩

lemma zpow_hom (g : G) (a b : ℤ) : g^a * g^b = g^(a + b) :=
begin
  unfold has_pow.pow,
  unfold zpow',
  rw add_comm,
  rw int.iterate.add,
  unfold function.comp,
  rw foo,
end



/-- The subgroup generated by an element of a group equals the set of integer number powers of
    the element. -/
lemma mem_span_singleton {x y : G} : y ∈ span ({x} : set G) ↔ ∃ n : ℤ, x ^ n = y :=
begin
  sorry
end



end subgroup

end mygroup

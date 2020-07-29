-- Iteration of equivalences over the integers

-- Idea -- if f is a bijection then we can talk about f^n for n an integer,
-- because f⁻¹ is just the inverse bijection

import tactic

namespace int

-- First we define f^n as a function
-- This is the n'th iterate of f as a function from X to X

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

lemma comp : int.iterate m f (int.iterate n f x) = int.iterate (m + n) f x :=
begin
  suffices : (f^m * f^n) x = (f^(m+n)) x,
    convert this,
  rw gpow_add,
end

@[simp] lemma zero : iterate 0 f = equiv.refl X := rfl
@[simp] lemma one : iterate 1 f = f := by {ext x, refl}
@[simp] lemma neg_one : iterate (-1) f = f.symm := by {ext x, refl}
--funext $ λ x, --funext $ λ x, rfl -- :-)

lemma neg (a : ℤ) : iterate (-a) f = iterate a f.symm :=
by show f^(-a) = f⁻¹^a; group

lemma succ : iterate n f (f x) = iterate (n + 1) f x := comp n 1 f x

theorem mul (f : X ≃ X) (a b : ℤ) (x : X) : iterate a (iterate b f) = 
int.iterate (a * b) f := by show (f^b)^a = f^(a*b); group

end iterate

end int

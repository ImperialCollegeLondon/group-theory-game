-- I'm thinking about finiteness

import tactic

import data.set.finite

/-
Reid said


def finite {a : Type} (s : set a) : Prop := -- any definition of finiteness

structure finset (a : Type) :=
(s : set a)
(h : finite s)

class fintype (a : Type) : Prop :=
(h : finite (set.univ : set a))

Mario said that this version of fintype is just
equivalent to current `nonempty fintype`

OK so I'll type

There's a big problem with fintype
It was written by computer scientists
and so it's data

In Lean there are two universes

Type and Prop

This is a lie, there are infinitely universes
because there is Type, Type 1, Type 2, Type 3, ...
but we don't really care about them
we can just think of them as all Type

So if `P : Prop` then P is a true-false statement
and if `h : P` then `h` is a proof

-- I think h isn't data, it's a proof

and if `T : Type` then T is data
and if `x : T` then x is data too

Examples : `ℝ : Type` and `π : ℝ` are data

So how about being finite?

There's finite
finset
and fintype

-/

variable X : Type

-- set.finite is a function which makes STATEMENTS

-- you can't prove something is finite with set.finite
-- you use the function set.finite to make the STATEMENT
-- that something is finite

-- set.finite : set X → Prop
-- You give it a set and it spits out a STATEMENT not a proof
-- it spits out a term of type Prop.



#check @set.finite X -- set.finite : set X → Prop

-- set.finite is unbundled finite sets
-- this function eats a set and returns whether or not it's finite

-- it's a Prop. It eats a subset of X and returns 
-- true or false

#check @finset X -- finset X : Type

-- this is bundled finite sets
-- This is a structure consisting of a set and
-- a proof that it's finite

-- finite subsets of X
-- Reid's proposal for finset
@[ext] structure FS1 (X : Type) :=
(S : set X)
(h : set.finite S)



#check FS1 X --  a type -- it's "the set of all finite subsets of X"

-- `evens` is the set of even natural numbers
def evens : set ℕ := {n : ℕ | ∃ k, n = 2 * k}

-- set ℕ -- the type of subsets of ℕ

-- this function `set` should have three names
-- depending on how we're thinking about it

-- `set ℕ` is the following three things.
/-

1) `set ℕ` is the type of subsets of ℕ 
   [ note: `subgroup G` is the type of subgroups of G]
   [ so why isn't `set ℕ` called `subset ℕ`? ]

2) a term of type `set ℕ` is a set of natural numbers!
  [ so now it looks it has a really nice name ]

3) `set ℕ` is the power set of ℕ -- it's the set of all subsets of ℕ
  [ so why isn't it called `powerset ℕ`? ]

  -- because the power set of ℕ is exactly this
  -- it's the set of all subsets of ℕ
-/

-- evens is the set of even natural numbers
#check evens 

-- We can ask if this set is finite

#check set.finite evens -- that's a true-false statement

-- evens.finite : Prop

-- evens.finite is a clever abbreviation for set.finite evens
-- because evens has type set ℕ, so evens.finite is an abbreviation for
-- set.finite evens

#check 2+2=5 -- Prop

-- Lean doesn't care if these propositions are true or false
-- it just gives a way of stating them

-- so `set.finite` is just the *statement* that a set is finite

open set

#print set.finite.to_finset

-- finset is "constructive finite sets"
-- to make a term of type `finset ℕ` Lean would like
-- to internally store a list of all the elements

noncomputable def bartonfinset_equiv_finset : FS1 X ≃ (finset X) :=
{ to_fun := λ T, set.finite.to_finset T.h,
  inv_fun := λ F, 
  { S := (↑F : set X), -- needs the uparrow
    h := finite_mem_finset F },
  left_inv := begin
    intro T,
    cases T with S h,
    ext x,
    apply finite.mem_to_finset,
  end,
  right_inv := begin
    intro F,
    dsimp,
    ext x,
    set S : set X := ↑F,
    rw ←(@finset.mem_coe _ _ F),
    rw finite.mem_to_finset
  end }

#check set.finite



-- conclusion -- we don't care about computability
-- we don't care about constructiveness

-- so we should be using `finite s` for finite sets
-- or Reid's bundled `finite s`


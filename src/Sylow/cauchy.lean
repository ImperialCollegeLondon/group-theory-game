import tactic 
import subgroup.theorems
import data.zmod.basic
import subgroup.cyclic
import data.vector2
import Sylow.prod_eq_one


/-!
# Cauchy's Theorem.

https://en.wikipedia.org/wiki/Cauchy%27s_theorem_(group_theory)

If a finite group $G$ has order a multiple of $p$ then
$G$ has an element of order $p$.

# Main Definitions.

## variables

(G : Type)
[group G]
(n : ℕ)

-/



namespace mygroup

open equiv fintype finset mul_action function
open equiv.perm mygroup.subgroup list mygroup.group


open_locale big_operators

universes u v w

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

/- want to prove the theorem that says
   that if p | |G| then G has an element of order p

   Proposed proof:

1) Let X be the set of lists of p elements of G whose product is 1 
  -- a definition and hence a stroke of genius.
  -- Status : DONE
2) Note that cyclic shift is a permutation of X
3) Note that #X=|G|^{p-1} is a multiple of p
4) Hence # fixed point is a multiple of p by some standard theorem
5) and # fixed points is at least 1 (the identity)
6) so it's at least 2 and there's an element of order p

-/

-- #check array -- for computing

/-! # making X -/

variables {G : Type} [group G]

--#check @mul_left_inj
--#check @mul_right_cancel_iff

open mygroup.group

lemma group.mul_left_inj : ∀ (a b c : G), b * a = c * a ↔ b = c :=
mul_right_cancel_iff

lemma group.inv_mul_self (a : G) : a⁻¹ * a = 1 := group.mul_left_inv a

instance : is_associative G (*) := ⟨group.mul_assoc⟩

open list

lemma list.prod_cons (a : G) (l : list G) : list.prod (a :: l) = a * l.prod :=
calc (a::l : list G).prod = foldl (*) (a * 1) l :
  by simp only [list.prod, foldl_cons, group.one_mul, group.mul_one]
  ... = _ : foldl_assoc


theorem cauchy (G : Type) [group G] [fintype G] (p : ℕ) (hp : p.prime)
  (hpG : p ∣ fincard' G) : ∃ H : subgroup G, fincard' H = p := 
begin
  sorry
end

end mygroup

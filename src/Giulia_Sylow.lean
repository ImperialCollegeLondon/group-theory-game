import group_theory.subgroup data.fintype.basic
import tactic -- remove once library_search bug is fixed
import group_theory.group_action
import data.nat.prime
import data.nat.modeq
import orbit.random 
noncomputable theory

open set classical
open function fintype
local attribute [instance] prop_decidable

namespace action

variables {G : Type*} [group G] {S : Type*}
variables {μ : laction G S}
variables (a b c s: S)
variables (g h : G)
def orbit_rel : setoid S :=
{ r := λ a b, a ∈ orbit μ b,
  iseqv := ⟨begin
   intro a,
   use (1 : G),
   rw μ.map_one,
  end, 
  begin
   intros a b h,
   cases h with g hg,
   rw hg,
   use g⁻¹ ,
   rw [μ.map_assoc, mul_left_inv, μ.map_one],
  end,
  begin
   intros a b c ha hb,
   cases ha with g1 hg1,
   cases hb with g2 hg2,
   use g1*g2,
   rw [hg1, ← μ.map_assoc, ← hg2],
  end⟩ 
    }
#check orbit
--Defining the set of fixed points of the action G on S. They form a subset of S.
@[reducible] def fixed_points (μ : laction G S) : set S:=
{s : S | ∀ g : G, μ.1 g s = s }

#check @fixed_points
--Dependent instance doesn't work
--instance : has_scalar G S := ⟨ λ g s, μ.1 g s ⟩
--#print notation • #exit 
local notation g ` • ` s := μ.1 g s 

notation g ` •[` μ `] ` s := μ.1 g s 
@[simp]lemma mem_fixed_points_iff : s ∈ fixed_points μ ↔ ∀ (g : G) , (g • s) = s := by refl 

--Want to show that if s is in the set of fixed points of μ, then the orbit of s contains only s.#check
lemma orbit_eq_singleton {g : G}{s : S} (μ : laction G S) : 
(s ∈ fixed_points μ) → orbit μ s = {s} := 
begin
  intro h,
  ext x, 
  simp * at *, 
end
localized "notation `∑` binders `, ` r:(scoped:67 f, finset.sum finset.univ f) := r" in big_operators
localized "notation `∑` binders ` in ` s `, ` r:(scoped:67 f, finset.sum s f) := r" in big_operators
variable [fintype G]
lemma finite_orbit' [fintype G] {a : S} : finite (orbit μ a) :=
begin
  split, split,
    swap, 
    { apply finset.image,
      exact λ g, ⟨μ.1 g a, g, rfl⟩,
      exact (univ : set G).to_finset },
    { simp, -- Nonterminating simp! I promise I will fix it!
      rintro x ⟨g, rfl⟩,
      refine ⟨g, rfl⟩ }
end
def foo  := {o | ∃ (s : S) (h : @card(orbit μ s) finite_orbit.fintype > 1), 
@card (orbit μ s) finite_orbit.fintype = o}
def foo2 := {o | ∃ s : S, orbit μ s = o}
def foo3 (o) [h : fintype o] := card o  > 1
#check foo
lemma finite_foo : @finite ℕ (foo) := sorry
--If S is a finite group then card S = card fixed_points G S + Σcard Oᵢ , 
--where the sum runs over orbits of size > 1.
lemma card_set_eq_card_fixed_points_sum_card_orbits (μ : laction G S)
 [fintype S] : --how to write the different s_i in S? How to specify I only want the s_i 
 --whose orbit has size > 1?
 card S = card(fixed_points μ) + ∑ o in foo , id o := sorry
--TODO: write adequate indexing and express sum correctly
--set_option pp.implicit true 
--If G is a group with card pⁿ, where p is prime and n ≥ 1, S is a finite set acted upon by G, 
--then card S cong card fixed points of S mod p.

lemma card_set_congr_card_fixed_points_mod_prime (μ : laction G S) 
 [fintype S] [fintype G] (p : ℕ) (hp : p.prime) (n : ℕ) (hn : n ≥ 1) (hG: card G = p^n):
 nat.modeq p (card S) (card (fixed_points μ) ) := 
 begin
  -- we want to show that card (orbit μ s) ∣ p^n for all s : S by orbit-stabilizer
  -- note that since G is finite we have finite orbits
  have claim : ∀ s : S, card( orbit μ s ) ∣ p^n , 
    {intro s, rw ← hG,
    use (card (stabilizer μ s)),
    rw @orbit_stabilizer G _ S _ s μ , congr,
    },
  sorry  
 end
--A p-group is a group s.t. all its elements have order a power of p, p prime
--def p_group (g : G) (p : ℕ ) (h : prime p) : sorry 
/-OR SHOULD I MAKE IT A CLASS? Using previous definition of group structure-/
#exit
theorem cauchy_theorem [group G][G fintype]( p : ℕ ) (hp : p.prime) (h : p ∣ (card G)): sorry
 --∃ (g : G) /-order of g is p-/ := sorry

end action

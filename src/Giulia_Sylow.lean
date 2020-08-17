import group_theory.subgroup data.fintype.basic
import tactic -- remove once library_search bug is fixed
import group_theory.group_action
import data.nat.prime
import data.nat.modeq
import subgroup.lagrange
import orbit.orbit_stabilizer
import data.finsupp

noncomputable theory

open set classical
open function fintype

open_locale classical

namespace mygroup

namespace action

variables {G : Type} [group G] {S : Type}
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
   change b = g⁻¹ • (g • b),
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
lemma orbit_eq_singleton {s : S} (μ : laction G S) : 
(s ∈ fixed_points μ) → orbit μ s = {s} := 
begin
  intro h,
  ext x, 
  simp * at *, 
end

--Is it worth proving? Should make iff?
lemma singleton_eq_orbit  {s : S} (μ : laction G S) : (orbit μ s = {s}) → s ∈ fixed_points μ :=
begin
  intros h k, 
  apply mem_singleton_iff.1 ,
  rw ← mem_singleton_iff at h,
  simp at *,
  apply singleton_eq_singleton_iff.1,
  rw ← h,
  refine ext _,
  intro x, split,
  {intro hx,
    refine singleton_subset_iff.mp _,
    simp at *,
    use k, exact hx},
  {intro hx, 
    refine mem_singleton_of_eq _,
    rw h at hx,
    rw mem_singleton_iff at hx,
    rw hx,
    symmetry,
    apply mem_singleton_iff.1,
    rw ← h,
    simp, use k}
end

--localized "notation `∑` binders `, ` r:(scoped:67 f, finset.sum finset.univ f) := r" in big_operators
--localized "notation `∑` binders ` in ` s `, ` r:(scoped:67 f, finset.sum s f) := r" in big_operators
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
#exit
--The idea is to define the set of elements in S whose orbit has cardinality greater than 1
def foo  := {o | ∃ (s : S) (h : @card(orbit μ s) finite_orbit.fintype > 1), 
@card (orbit μ s) finite_orbit.fintype = o}
def foo2 := {o | ∃ s : S, orbit μ s = o}
def foo3 (o) [h : fintype o] := fincard o  > 1
#check foo

lemma finite_foo : @finite ℕ (foo) := sorry

--WAS TRYING TO IMPLEMENT SIMILAR PROCEDURE AS ABOVE, BUT DEFINING foo' : set S.
--def foo' := {s : S |  @card(orbit μ s) finite_orbit.fintype > 1}
--#check foo'
--lemma finite_foo' : finite (foo') := sorry
/-lemma card_set_eq_card_fixed_points_sum_card_orbits' (μ : laction G S) 
 [fintype S] : card S = card(fixed_points μ) + ∑ card(orbit μ (s in foo') ) := sorry -/


--If S is a finite group then card S = card fixed_points G S + Σcard Oᵢ , 
--where the sum runs over orbits of size > 1.

lemma card_set_eq_card_fixed_points_sum_card_orbits (μ : laction G S)
 [fintype S] : fincard S = fincard(fixed_points μ) + ∑ o in foo , id o := sorry
--TODO: write adequate indexing and express sum correctly



--If G is a group with card pⁿ, where p is prime and n ≥ 1, S is a finite set acted upon by G, 
--then card S cong card fixed points of S mod p.

lemma card_set_congr_card_fixed_points_mod_prime (μ : laction G S) 
 [fintype S] [fintype G] (p : ℕ) (hp : p.prime) (n : ℕ) (hn : n ≥ 1) (hG: card G = p^n):
 nat.modeq p (fincard S) (fincard (fixed_points μ) ) := 
 begin
  -- we want to show that card (orbit μ s) ∣ p^n for all s : S by orbit-stabilizer
  -- note that since G is finite we have finite orbits
  have claim : ∀ s : S, fincard( orbit μ s ) ∣ p^n , 
    {intro s, rw ← hG,
    use (fincard (stabilizer μ s)),
    rw @orbit_stabilizer G _ S _ s μ , congr,
    },
  sorry  
 end
--A p-group is a group s.t. all its elements have order a power of p, p prime
--def p_group (g : G) (p : ℕ ) (h : prime p) : sorry 
/-OR SHOULD I MAKE IT A CLASS? Using previous definition of group structure-/

theorem cauchy_theorem [group G][fintype G] {p : ℕ} (hp : p.prime) (h : p ∣ (fincard G)): 
 ∃ (S : subgroup G), fincard S = p := sorry
--need to define order of an element
end action

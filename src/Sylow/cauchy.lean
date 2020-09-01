import tactic 
import subgroup.theorems
import data.zmod.basic
import subgroup.cyclic

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

* `array_prod_eq_one : set (vector G n)` : lists of length n in G whose product is 1

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

/-! # making X -/

--#check subtype.prod
def vector.prod_eq_one' (G : Type) [group G] (n : ℕ) : set (vector G n) :=
{v : vector G n | v.to_list.prod = 1}

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def array_prod_eq_one (G : Type*) [group G] (n : ℕ) : set (fin n → G) :=
{f | (list.of_fn f).prod = 1}

variables {G : Type} [group G]

--#check @mul_left_inj
--#check @mul_right_cancel_iff

open mygroup.group

lemma group.mul_left_inj (a b c : G) : b * a = c * a ↔ b = c :=
begin
  --  **TODO(anyone)** -- why can't we remove "group" here?
  exact mul_right_cancel_iff a b c,
end

--#check @inv_mul_self

lemma group.inv_mul_self (a : G) : a⁻¹ * a = 1 := group.mul_left_inv a

instance : is_associative G (*) := ⟨group.mul_assoc⟩

open list

lemma list.prod_cons (a : G) (l : list G) : list.prod (a :: l) = a * l.prod :=
calc (a::l : list G).prod = foldl (*) (a * 1) l :
  by simp only [list.prod, foldl_cons, group.one_mul, group.mul_one]
  ... = _ : foldl_assoc

/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
@[reducible] def vector.to_succ_prod_eq_one {n : ℕ} (v : vector G n) : vector G (n+1) :=
v.to_list.prod⁻¹ :: v

--Is something missing here? Should we turn mk_vector_prod_eq_one into a list or a set?
--Copied the following bit from library
lemma vector.to_succ_prod_eq_one_injective (n : ℕ) :
  injective (@vector.to_succ_prod_eq_one G _ n) :=
λ ⟨v, _⟩ ⟨w, _⟩ h, subtype.eq (show v = w, by injection h with h; injection h)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
@[reducible] def vector.prod_eq_one (G : Type) [group G] (n : ℕ) : set (vector G n) :=
{v | v.to_list.prod = 1}

lemma mem_vectors_prod_eq_one {n : ℕ} (v : vector G n) :
  v ∈ vector.prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

--#print vector.tail
/-
def vector.tail : Π {α : Type u} {n : ℕ}, vector α n → vector α (n - 1) :=
λ {α : Type u} {n : ℕ}, vector.tail._main
-/
--def vector.tail' {α : Type u} {n : ℕ} : vector α n.succ → vector α n :=
--vector.tail

lemma mem_vectors_prod_eq_one_iff {n : ℕ} (v : vector G (n + 1)) :
  v ∈ vector.prod_eq_one G (n + 1) ↔
  v ∈ set.range (vector.to_succ_prod_eq_one : vector G n → vector G (n + 1)) :=
⟨λ (h : v.to_list.prod = 1), ⟨v.tail,
  begin
    rcases v with ⟨l, hl⟩,
    cases l with h t, cases hl,
    simp at h,
    simp [vector.tail],
    apply vector.to_list_injective,
    simp,
    rw list.prod_cons at h,
    apply mul_right_cancel t.prod,
    rw h,
    simp,
  end⟩, 
  begin
    rintro ⟨⟨l, hl⟩, rfl⟩,
    simp [list.prod_cons],
  end⟩
  
/-- The rotation action of `zmod n` (viewed as multiplicative group) on
`vectors_prod_eq_one G n`, where `G` is a multiplicative group. -/

def cyclic.generator {n : ℕ} : cyclic n := quotient.mk _ (1 : ℤ)

lemma cyclic.generator_generates (n : ℕ) :
  closure ({cyclic.generator} : set (cyclic n)) = ⊤ :=
sorry
--{(@cyclic.generator n : cyclic n)} = ⊤ := sorry

def rotate_vectors_prod_eq_one (G : Type) [group G] (n : ℕ)
  (m : cyclic n) (v : vector.prod_eq_one G n) : vector.prod_eq_one G n :=
sorry
--⟨⟨v.1.to_list.rotate m.val, by simp⟩, prod_rotate_eq_one_of_prod_eq_one v.2 _⟩

--Need to understand exactly what is going on in the term mode proof and why it does not work here
--Make a cyclic group of order n, called Cₙ

instance rotate_vectors_prod_eq_one.mul_action (n : ℕ) [fact (0 < n)] :
  mul_action (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
{ smul := (rotate_vectors_prod_eq_one G n),
  one_smul :=
  begin
    intro v, apply subtype.eq, apply vector.eq _ _,
    sorry
    -- show rotate _ (0 : zmod n).val = _, rw zmod.val_zero,
    -- exact rotate_zero v.1.to_list
  end,
  mul_smul := λ a b ⟨⟨v, hv₁⟩, hv₂⟩, subtype.eq $ vector.eq _ _ $
  sorry
--    show v.rotate ((a + b : zmod n).val) = list.rotate (list.rotate v (b.val)) (a.val),
--    by rw [zmod.val_add, rotate_rotate, ← rotate_mod _ (b.val + a.val), add_comm, hv₁] 
}

lemma one_mem_vectors_prod_eq_one (n : ℕ) : vector.repeat (1 : G) n ∈ vectors_prod_eq_one G n :=
sorry
--by simp [vector.repeat, vectors_prod_eq_one]


-- lemma one_mem_fixed_points_rotate (n : ℕ) [fact (0 < n)] :
--   (⟨vector.repeat (1 : G) n, one_mem_vectors_prod_eq_one n⟩ : vectors_prod_eq_one G n) ∈
--   fixed_points (multiplicative (zmod n)) (vectors_prod_eq_one G n) :=
-- λ m, subtype.eq $ vector.eq _ _ $
-- rotate_eq_self_iff_eq_repeat.2 ⟨(1 : G),
--   show list.repeat (1 : G) n = list.repeat 1 (list.repeat (1 : G) n).length, by simp⟩ _

end mygroup

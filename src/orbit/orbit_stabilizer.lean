import subgroup.lagrange
import data.nat.modeq -- added by Giulia
import data.nat.prime  -- added by Giulia
open set classical function

open_locale classical

noncomputable theory

namespace mygroup

/-- A left action of some group `G` on some `S` is a function with type 
  `to_fun : G → S → S` such that for all `s : S`, `to_fun 1 s = 1` and for all 
  `g, h : G`, `s : S`, `to_fun g (to_fun h s) = to_fun (g * h) s` -/
structure laction (G : Type) [group G] (S : Type) :=
(to_fun    : G → S → S) (map_one' : ∀ s : S, to_fun 1 s = s)
(map_assoc' : ∀ g h : G, ∀ s : S, to_fun g (to_fun h s) = to_fun (g * h) s)

variables {G S : Type} [group G]
variables {μ : laction G S}

notation g ` •[`:70 μ `] `:0 s:70 := μ.to_fun g s
local notation g ` • `:70  s:70  := μ.to_fun g s

namespace laction

-- APIs for left actions 

@[simp] lemma map_one (μ : laction G S) (s : S) : (1 •[μ] s) = s := μ.map_one' _

lemma map_assoc (g h : G) (s : S) : g • (h • s) = g * h • s := 
  μ.map_assoc' _ _ _

-- The user should prove these two lemmas below

lemma laction_mul_inv_cancel {g h : G} {s : S} : 
  g • s = h • s ↔ s = (g⁻¹ * h) • s :=
begin
  split; intro hgh,
    { conv_lhs { rw ←map_one μ s }, 
      rw [←(group.mul_right_inv g⁻¹), ←map_assoc, 
          ←map_assoc, ←hgh, group.inv_inv] },
    { conv_lhs { rw [hgh, map_assoc, ←group.mul_assoc, 
                     group.mul_right_inv, group.one_mul] } }
end

lemma laction_mul_inv {g : G} {s t : S} : g • s = t ↔ s = g⁻¹ • t :=
begin
  split; intro h,
    rw [←h, map_assoc, group.mul_left_inv, map_one],
    rw [h, map_assoc, group.mul_right_inv, map_one]
end

end laction

/-- The orbit of some element of `s : S` is the image of the left action at `s` -/
def orbit (μ : laction G S) (s : S) : set S := 
  { m : S | ∃ g : G, m = g •[μ] s } 

local notation `💫`:70 s:70 := orbit μ s

namespace laction

@[simp]
lemma orbit_def {s : S} : 💫 s = { m : S | ∃ g : G, m = g • s } := rfl

@[simp]
lemma mem_orbit {s t : S} : t ∈ 💫 s ↔ ∃ g : G, t = g • s := 
by rw [orbit_def, mem_set_of_eq]

/-- An element of `G` is in its own orbit -/
lemma mem_orbit_refl (s : S) : s ∈ 💫 s := ⟨1, (map_one μ s).symm⟩

/-- If `s₁ : S` is in `s₂ : S`'s orbit, then `s₂` is in `s₁`'s orbit -/
lemma mem_orbit_symm {s₁ s₂ : S} (h : s₁ ∈ 💫 s₂) : s₂ ∈ 💫 s₁ := 
let ⟨g, hg⟩ := h in ⟨g⁻¹, by rw [hg, map_assoc, group.mul_left_inv, map_one]⟩

/-- If s₁ ∈ [s₂] and s₂ ∈ [s₃] then s₁ ∈ [s₃] -/
lemma mem_orbit_trans {s₁ s₂ s₃ : S} 
  (hs₁ : s₁ ∈ 💫 s₂) (hs₂ : s₂ ∈ 💫 s₃) : s₁ ∈ 💫 s₃ :=
begin
  cases hs₁ with g₁ hg₁,
  cases hs₂ with g₂ hg₂,
  refine ⟨g₁ * g₂, _⟩,
  rw [hg₁, hg₂, map_assoc]
end

/-- If two elements of `S` are in the same orbit then they are in eachothers orbit-/
lemma in_orbit_of_in_same_orbit {s₁ s₂ s₃ : S} 
  (hs₁ : s₁ ∈ 💫 s₃) (hs₂ : s₂ ∈ 💫 s₃) : s₁ ∈ 💫 s₂ :=
begin
  cases hs₁ with g₁ hg₁,
  cases hs₂ with g₂ hg₂,
  refine ⟨g₁ * g₂⁻¹, _⟩,
  rw [hg₁, hg₂, map_assoc, group.mul_assoc, group.mul_left_inv, group.mul_one]
end

lemma in_orbit_of_inv' {s₁ s₂ : S} {g : G} (h : s₁ = g • s₂) : 
  s₂ = g⁻¹ • s₁ := by rw [h, map_assoc, group.mul_left_inv, map_one]

lemma eq_orbit {s₀ s₁ : S} (t : S) 
  (hs₁ : t ∈ 💫 s₀) (hs₂ : t ∈ 💫 s₁) : 💫 s₀ = 💫 s₁ :=
begin
  cases hs₁ with g₁ hg₁,
  cases hs₂ with g₂ hg₂,
  ext, split; rintro ⟨g, rfl⟩,
    { rw [hg₁, laction_mul_inv, map_assoc] at hg₂,
      rw [mem_orbit, hg₂, map_assoc],
      exact ⟨g * (g₁⁻¹ * g₂), rfl⟩ },
    { rw [hg₂, laction_mul_inv, map_assoc] at hg₁,
      rw [mem_orbit, hg₁, map_assoc],
      exact ⟨g * (g₂⁻¹ * g₁), rfl⟩ } 
end

end laction

/-- The stabilizer of `s : S` is the subgroup which elements fixes `s` under the 
  left laction -/
def stabilizer (μ : laction G S) (s : S) : subgroup G := 
{ carrier := { g : G | (g •[μ] s) = s },
  one_mem' := laction.map_one μ _,
  mul_mem' := λ _ _ hg hh, 
    by { rw mem_set_of_eq at *, rw [←laction.map_assoc, hh, hg] },
  inv_mem' := λ x hx, 
    begin
      rw mem_set_of_eq at *, 
      conv_lhs { rw ←hx },
      rw [laction.map_assoc, group.mul_left_inv _, μ.2] 
    end }

/-- Two subgroups `H K` of group `G` are conjugates if and only if there exist 
  some `g : G`, `g⁻¹ H g = K` -/
def is_conjugate (H K : subgroup G) := 
  ∃ g : G, { c | ∃ h ∈ H, c = g⁻¹ * h * g } = K

--  The normalizer of a subset of G is a subgroup of G 
def normalizer {A : set G} : subgroup G := 
{ carrier := {g : G | ∀ n, n ∈ A ↔ g * n * g⁻¹ ∈ A},
  one_mem' := 
    begin
      intro a,
      rw [group.one_mul, group.one_inv, group.mul_one],
    end,
  mul_mem' := 
    begin  
      intros x y hx hy a,
      dsimp at *,
      rw hy,
      rw hx,
      simp [group.mul_assoc],
    end,
  inv_mem' := 
    begin
      intros x hx a, 
      dsimp at *,
      rw hx (x⁻¹ * a * x⁻¹⁻¹),
      simp [group.mul_assoc],      
    end   
  }
/-def normalizer : subgroup G :=
{ carrier := {g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H},
  one_mem' := by simp,
  mul_mem' := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by { rw [hb, ha], simp [mul_assoc] },
  inv_mem' := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by { rw [ha (a⁻¹ * n * a⁻¹⁻¹)], simp [mul_assoc] } }-/
namespace laction

@[simp]
lemma mem_stabilizer (s : S) (g : G) : g ∈ stabilizer μ s ↔ g • s = s := iff.rfl

/-- If `H` is the conjugate of `K`, then `K` is the conjugate of `H` -/
lemma is_conjugate_comm {H K : subgroup G} (h : is_conjugate H K) :
  is_conjugate K H := 
begin
  cases h with g hg, refine ⟨g⁻¹, _⟩,
  ext, split; intro hx, 
    { rcases hx with ⟨h, hh₀, hh₁⟩,
      change h ∈ (K : set G) at hh₀,
      rw ←hg at hh₀,
      rcases hh₀ with ⟨k, hk₀, hk₁⟩,
      rw [hh₁, hk₁], simpa [group.mul_assoc] },
    { rw mem_set_of_eq,
      refine ⟨g⁻¹ * x * g, _, by simp [group.mul_assoc]⟩,
      show g⁻¹ * x * g ∈ (K : set G),
      rw ←hg, exact ⟨x, hx, rfl⟩ }
end

/-- If two elements are in the same orbit, then their stabilizers are conjugates -/
theorem conjugate_stabilizer_of_in_same_orbit {s₁ s₂ s₃ : S} 
  (hs₁ : s₁ ∈ 💫 s₃) (hs₂ : s₂ ∈ 💫 s₃) : 
  is_conjugate (stabilizer μ s₁) (stabilizer μ s₂) :=
begin
  cases in_orbit_of_in_same_orbit hs₁ hs₂ with g hg,
  refine ⟨g, _⟩,
  ext, split; intro hx,
    { show x ∈ stabilizer μ s₂,
      rcases hx with ⟨h, hh₀, hh₁⟩,
      rw [mem_stabilizer, hh₁, ←map_assoc, ←map_assoc, ←hg, 
         (show h • s₁ = s₁, by exact hh₀), hg, map_assoc, 
         group.mul_left_inv, map_one] },
    { change x ∈ stabilizer μ s₂ at hx, 
      refine ⟨g * x * g⁻¹, (mem_stabilizer _ _).2 _, _⟩,
      rw [←map_assoc, ←(in_orbit_of_inv' hg), 
          ←map_assoc, (mem_stabilizer _ _).1 hx, hg], by simp [group.mul_assoc] }
end

private structure extract_struct {μ : laction G S} {a : S} (s : orbit μ a) :=
(val : G) (prop : s.1 = μ.to_fun val a)

@[reducible] private def extract {μ : laction G S} {a : S} (s : orbit μ a) : 
  extract_struct s := ⟨some s.2, some_spec s.2⟩

@[reducible] private def aux_map (μ : laction G S) (a : S) : 
  orbit μ a → { s | ∃ h : G, s = h ⋆ stabilizer μ a } := 
λ s, ⟨(extract s).1 ⋆ stabilizer μ a, (extract s).1, rfl⟩

private lemma aux_map_biject {a : S} : bijective $ aux_map μ a :=
begin
  split,
    { rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy,
      rw [subtype.mk.inj_eq, lagrange.lcoset_eq] at hxy,
      change ((extract ⟨y, hy⟩).val)⁻¹ * (extract ⟨x, hx⟩).val ∈ 
        { g : G | g • a = a } at hxy,
      rw [mem_set_of_eq, ←μ.3, ←(extract ⟨x, hx⟩).2, 
        @laction_mul_inv _ _ _ μ _ x a, group.inv_inv, ←(extract ⟨y, hy⟩).2] at hxy,
      simp only [hxy] },
    { rintro ⟨_, g, hg⟩, refine ⟨⟨g • a, g, rfl⟩, _⟩,
      rw [subtype.mk.inj_eq, hg, lagrange.lcoset_eq],
      show g⁻¹ * (extract ⟨μ.to_fun g a, _⟩).val ∈ { g : G | g • a = a },
      rw [mem_set_of_eq, ←μ.3, ←(extract ⟨μ.to_fun g a, _⟩).2, 
        μ.3, group.mul_left_inv, μ.2] }
end 

-- With this function defined, we see that the cardinality of orbit s equals 
-- the number of left cosets of stabilizer s

lemma card_orbit_eq_num_lcoset {a : S} : 
  fincard' (orbit μ a) = fincard' { s | ∃ h : G, s = h ⋆ stabilizer μ a } :=
fincard.of_equiv (equiv.of_bijective _ aux_map_biject)

/-- Orbit-Stabilizer : The cardinality of a finite group `G` given a laction `μ` 
on some `S` equals the cardinality of the orbit of `s` multiplied by the 
cardinality of the stabilizer of `s` for any `s : S` -/
theorem orbit_stabilizer [h: fintype G] {a : S} (μ : laction G S) : 
  fincard' G = fincard' (orbit μ a) * fincard' (stabilizer μ a) := 
by rw [card_orbit_eq_num_lcoset, mul_comm]; exact lagrange.lagrange 

/-! # fixed points -/

end laction

def fixed_points (μ : laction G S) : set S := {s : S | ∀ g : G, g •[μ] s = s }

@[simp] lemma mem_fixed_points_iff (s : S) :
  s ∈ fixed_points μ ↔ ∀ (g : G) , g • s = s := iff.rfl

--Want to show that if s is in the set of fixed points of μ, then the orbit of s contains only s.#check
lemma orbit_eq_singleton {s : S} {μ : laction G S} (h : s ∈ fixed_points μ) : 
  orbit μ s = {s} := 
begin
  ext x, 
  simp * at *, 
end

lemma mem_fixed_points {s : S} {μ : laction G S} (h : orbit μ s = {s}) :
  s ∈ fixed_points μ :=
begin
  intros k,
  apply mem_singleton_iff.1,
  rw ←h,
  use k
end

lemma orbit_eq_singleton_iff {s : S} {μ : laction G S} :
  orbit μ s = {s} ↔ s ∈ fixed_points μ := ⟨mem_fixed_points, orbit_eq_singleton⟩

--The following lemma is based on the one by the same name in the library,
-- I believe it is needed to prove card_set_eq_card_fixed_points_sum_card_orbits
lemma mem_fixed_points_iff_card_orbit_eq_one {s : S} {μ : laction G S}:
  s ∈ fixed_points μ ↔ fincard' (orbit μ s) = 1 :=
begin
  rw ←orbit_eq_singleton_iff,
  split; intro h,
    { simp [h] },
    { rw eq_singleton_iff_unique_mem,
      refine ⟨laction.mem_orbit_refl _, λ y hy, _⟩,
      rcases fincard.card_eq_one_iff_singleton.1 h with ⟨x, hx⟩, 
      rw hx at hy,
      rw [mem_singleton_iff.1 hy, ←mem_singleton_iff, ←hx],
      exact laction.mem_orbit_refl _ }
end

/-
S : Type
~ : equiv reln on S
Common in maths departments to let Q = set of equiv classes

Map cl : S -> Q, sends s to cl(s) = {t : t ~ s}

What key properties do Q and S -> Q have?

Key one is the "universal property"

  If g : S -> T
  and if g has the following property : it's constant on equiv classes
  i.e. s1 ~ s2 -> g(s1) = g(s2) (*)

  then there's a map g-bar from Q to T "induced by g"

    Definition of g-bar: let q ∈ Q be an equiv class
    q ⊆ S and is nonempty
    choose s ∈ q <- MADE A CHOICE
    define g-bar(q) := g(s)
    What if I'd instead chosen s' ∈ q, s' ≠ s?
    Then g(s)=g(s') by our assumption (*)
    hence g-bar(q) doesn't depend on choice of s

   Hence "g-bar is well-defined"

Furthermore, S --(g)--> T
             |       /\   
             |      /    
            (cl)  (g-bar)     
             |    /      
             \/  /       
             Q -/

/-

             g = g-bar ∘ cl

That's a property that cl has

Conversely, if I have φ : Q -> T then I can compose with cl and
get a map φ-tilde = φ ∘ cl : S -> T and I claim that if s1 and s2 are in S with s1 ~ s2
then φ-tilde (s1) = φ-tilde (s2) (i.e. φ-tilde satisfies (*) above)

So now we have two maps between the following sets:

1) {g : S → T | if s1 ~ s2 then g(s1) = g(s2) }
2) {φ : Q → T}

Map from 1 to 2 sends g to g-bar
Map from 2 to 1 sends φ to φ-tilde = φ ∘ cl

Easy to check that these are inverse bijections

In particular, we have cl : S → Q and composing with cl
gives us a bijection from {Q → T} to {g : S → T | g satisfies (*)}

Turns out that this characterises Q, the set of equiv classes, up to unique isomorphism
and hence this bijection property can be used as a "definition of Q" in some sense

In particular, Q doesn't _have_ to be equivalence classes! 

Given S and an equiv reln, I now think of Q not as the set of equiv classes
but as any set at all with a surjection from S satisfying this property.

Annoyingly, my mental model of g-bar is "going downwards" but in Lean they
call it quotient.lift

equiv reln on S
Q = quotient = type of equiv classes

-/

-- should now prove that for G acting on S, size of S = sum
-- of size of orbits.

/-- Orbits of an action -/
def orbits (μ : laction G S) := setoid.classes
  {r := λ (x y : S), x ∈ orbit μ y,
   iseqv := ⟨laction.mem_orbit_refl,
            λ x y, laction.mem_orbit_symm,
            λ x y z, laction.mem_orbit_trans⟩}

lemma orbit_mem_orbits (s : S) : orbit μ s ∈ orbits μ := ⟨s, rfl⟩

lemma orbit_unique {x : S} {s : set S} (hs : s ∈ orbits μ) : 
  x ∈ s ↔ orbit μ x = s :=
begin
  unfold orbits at hs,
  change s ∈ {s | ∃ y, s = {x | x ∈ orbit μ y}} at hs,
  rcases hs with ⟨y, rfl⟩,
  split; intro hx,
    { change x ∈ orbit μ y at hx,
      exact laction.eq_orbit x (laction.mem_orbit_refl _) hx },
    { change orbit μ x = orbit μ y at hx,
      rw ←hx, exact laction.mem_orbit_refl _ }
end

lemma sum_card_orbits [fintype S] : ∑' o in (orbits μ), fincard' o = fincard' S :=
(fincard.card_eq_finsum_partition (setoid.is_partition_classes _)).symm

/-
def orbits_not_singleton (μ : laction G S): set (orbits μ) := {o : orbits μ | fincard' o > 1}

--Should I rewrite the fixed points as a collection of singletons?
def singleton_orbits  (μ : laction G S) : set (orbits μ) := {o : orbits μ | fincard' o = 1}
--It probably makes more sense to write it as the following lemma, though fixed_points is a subset of S 
-- and {o : orbits μ | fincard' o = 1} is a subset of orbits  ↥

lemma fixed_points_singletons [fintype S] (μ : laction G S) : 
  ↥(fixed_points μ) = (singleton_orbits μ ) := 
begin
 unfold fixed_points,
 unfold singleton_orbits,
 sorry
end  

--The issue here is that types are different
lemma foo [fintype S] (μ : laction G S):
orbits μ = (orbits_not_singleton μ) ∪ singleton_orbits μ  := sorry 
-/

lemma dumb {n : ℕ} (hn : n ≤ 1) : n = 0 ∨ n = 1 := 
begin
  induction n, finish,
  rw nat.succ_le_iff at hn,
  change _ < 1 + 0 at hn,
  rw nat.lt_one_add_iff at hn,
  rw nat.le_zero_iff at hn,
  right, rw hn,
end

lemma card_orbits_eq_one [fintype S] {s : set S} 
  (hs₀ : s ∈ orbits μ) (hs₁ : fincard' s ≤ 1) : fincard' s = 1 :=
begin
  cases dumb hs₁,
    { change s ∈ {s | ∃ y, s = {x | x ∈ orbit μ y}} at hs₀,
      rcases hs₀ with ⟨x, hx⟩,
      change s = orbit μ x at hx,
      rw fincard.card_eq_zero_iff at h,
      exfalso,
      apply not_mem_empty x,
      rw [←h, hx],
      exact laction.mem_orbit_refl x },
    { assumption }
end

def map_singleton (μ : laction G S) : (fixed_points μ) → 
  ({o ∈ orbits μ | fincard' o ≤ 1} : set (set S)) :=
λ s, ⟨orbit μ s, orbit_mem_orbits _,
  let ⟨_, hs⟩ := s in le_of_eq (mem_fixed_points_iff_card_orbit_eq_one.1 hs)⟩

@[simp] lemma map_singleton_def (s : S) (hs : s ∈ fixed_points μ) : 
  (map_singleton μ ⟨s, hs⟩ : set S) = {s} :=
begin
  suffices : {m : S | ∃ (g : G), m = g • s} = {s},
    simpa [map_singleton], 
  finish,
end

lemma bijective_map_singleton [fintype S] (μ : laction G S) : 
  function.bijective (map_singleton μ) :=
begin
  split,
    { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, congr,
      rw ←singleton_eq_singleton_iff,
      iterate 2 { rw ←map_singleton_def _ }, rw hxy },
    { rintros ⟨y, hy₀, hy₁⟩,
      rcases fincard.card_eq_one_iff_singleton.1 
        (card_orbits_eq_one hy₀ hy₁) with ⟨x, rfl⟩,
      refine ⟨⟨x, _⟩, _⟩,
        { rw ←orbit_eq_singleton_iff,
          exact (orbit_unique hy₀).1 (mem_singleton _) },
        { suffices : {m : S | ∃ (g : G), m = g • x} = {x},
            simpa [map_singleton],
          suffices : x ∈ fixed_points μ,
            finish,
          rw ←orbit_eq_singleton_iff,
          exact (orbit_unique hy₀).1 (mem_singleton _) } }
end

lemma card_fixed_points [fintype S] : fincard' (fixed_points μ) = 
  let p := λ s : set S, fincard' s ≤ 1 in
  ∑' o in { o ∈ orbits μ | p o }, fincard' o := 
begin
  dsimp only,
  rw @finsum_const_nat (set S) (by apply_instance) _ 1 _,
    { rw mul_one,
      exact fincard.of_equiv (equiv.of_bijective _ $ bijective_map_singleton μ) },
    { exact λ x ⟨hx₀, hx₁⟩, card_orbits_eq_one hx₀ hx₁ },
end

lemma card_set_eq_card_fixed_points_sum_card_orbits [fintype S] (μ : laction G S): 
  fincard' S = fincard' (fixed_points μ) 
             + let p := λ s : set S, fincard' s ≤ 1 in
             ∑' o in { o ∈ (orbits μ) | ¬ p o }, fincard' o := 
begin
  rw [card_fixed_points, fincard.finsum_in_filter],
  exact sum_card_orbits.symm
end

--I don't think this is needed anymore
lemma pow_prime_eq_one_or_dvd_prime {p d n : ℕ }(hp: p.prime) (hd: d = p^n): d = 1 ∨ p ∣ d := 
begin
  cases n,
  left, 
  simpa,
  right,
  rw hd,
  simp [nat.succ_eq_add_one, nat.pow_succ]
end
 

/- This lemma is dvd_prime_pow
lemma foo_two {p d n : ℕ }(hp: p.prime) (hd: d ∣ p^n): ∃ (m ≤ n), d = p^m := 
begin
  induction n with hn,
  rw nat.pow_zero at hd,
  use 0, 
  split,
  linarith,
  rw nat.pow_zero, 
  exact nat.dvd_one.mp hd,
  rw nat.succ_eq_add_one at *,
  exact (nat.dvd_prime_pow hp).mp hd  
end  -/

--Are these names okay? Should I leave these lemmas here?
lemma card_orbit_div_pow_p (μ : laction G S) 
 [fintype S] [fintype G](p : ℕ) (hp : p.prime) (n : ℕ) (hG: fincard' G = p^n):
 ∀ s : S, fincard'( orbit μ s ) ∣ p^n :=
 begin
   intro s, rw ← hG,
    use (fincard' (stabilizer μ s)),
    rw laction.orbit_stabilizer,
 end  

lemma card_orbit_eq_one_or_dvd_p (μ : laction G S) 
[fintype S] [fintype G](p : ℕ) (hp : p.prime) (n : ℕ) (hG: fincard' G = p^n): 
∀ (s : S), fincard' ↥(orbit μ s) = 1 ∨ p ∣ fincard' ↥(orbit μ s) :=
begin
  intro s,
    cases (card_orbit_div_pow_p μ p hp n hG) s with _ _,
    have h1: fincard' ↥(orbit μ s) ∣ p^n,
    { use w, exact h },
    rw nat.dvd_prime_pow hp at h1,
    rcases h1 with ⟨ a, _, ha ⟩ , 
    rw ha,
    cases a with _ _,
    rw nat.pow_zero,
    left, 
    refl,
    right,
    rw nat.pow_succ,
    use p^a,
    rw mul_comm,
end  



lemma card_set_congr_card_fixed_points_mod_prime (μ : laction G S) 
 [fintype S] [fintype G](p : ℕ) (hp : p.prime) (n : ℕ) (hG: fincard' G = p^n):
 nat.modeq p (fincard' S) (fincard' (fixed_points μ) ) := 
 begin
  have claim : ∀ s : S, fincard'( orbit μ s ) ∣ p^n , 
    { exact card_orbit_div_pow_p μ p hp n hG },
  rw card_set_eq_card_fixed_points_sum_card_orbits μ,
  dsimp,
  refine nat.modeq.modeq_of_dvd _,
  suffices: ↑p ∣ ↑∑' (o : set S) in ({o ∈ orbits μ | 1 < fincard' ↥o} : set (set S)), fincard' ↥o,
    { simpa [sub_eq_add_neg] },
  norm_cast,
  apply fincard.finsum_divisible_by,
  have: ∀ (s : S), fincard' ↥(orbit μ s) = 1 ∨ p ∣ fincard' ↥(orbit μ s),
    { exact card_orbit_eq_one_or_dvd_p μ p hp n hG },
  rintro x h,
  cases h with hl hr,
  cases hl with s hs,
  change x = orbit μ s at hs,
  rw hs,
  cases this s,
  rw [hs, h] at hr,
  linarith,
  assumption
 end



--Definition of p-group for finite groups, not using definition of order of an element explicitly
-- The following definition should be stated as an iff corollary
--does it hold with n ≥ 0?
class p_group [fintype G] {p : ℕ}{hp: p.prime}{n : ℕ}{hn : n ≥ 1} extends group G :=
(card_pow_p: fincard' G = p^n)

--A p-subgroup is a subgroup of a group G which is itself a p-group
class p_subgroup [fintype G][H : subgroup G] {p : ℕ}{hp: p.prime}{n : ℕ}{hn : n ≥ 1} extends subgroup G :=
(card_pow_p: fincard' (set H) = p^n)


end mygroup
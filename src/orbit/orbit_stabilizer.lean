import subgroup.lagrange

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

-- Is this really not in the library?
lemma eq_singleton_iff_unique_mem {X : Type} {x : X} {s : set X} : 
  s = {x} ↔ x ∈ s ∧ ∀ y ∈ s, x = y :=
begin
  split,
    { rintro rfl, simp },
    { rintro ⟨h₀, h₁⟩,
      ext, split; finish }
end

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
      rcases (fincard.card_eq_one_iff_singleton _).1 h with ⟨x, hx⟩, 
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

lemma sum_card_orbits [fintype S] : ∑' o in (orbits μ), fincard' o = fincard' S :=
(fincard.card_eq_finsum_partition (setoid.is_partition_classes _)).symm

def orbits_not_singleton (μ : laction G S): set (orbits μ) := {o : orbits μ | fincard' o > 1}

--Should I rewrite the fixed points as a collection of singletons?
def singleton_orbits  (μ : laction G S) : set (orbits μ) := {o : orbits μ | fincard' o = 1}
--It probably makes more sense to write it as the following lemma, though fixed_points is a subset of S 
-- and {o : orbits μ | fincard' o = 1} is a subset of orbits  ↥

#check fixed_points μ 
#check singleton_orbits μ 
#check orbits_not_singleton μ 
#check orbits μ 

lemma fixed_points_singletons [fintype S] (μ : laction G S) : 
↥(fixed_points μ) = (singleton_orbits μ ) := 
begin
 unfold fixed_points,
 unfold singleton_orbits,
 sorry
end  

#exit
--The issue here is that types are different
lemma foo [fintype S] (μ : laction G S):
orbits μ = (orbits_not_singleton μ) ∪ singleton_orbits μ := sorry 


lemma card_set_eq_card_fixed_points_sum_card_orbits [fintype S] : fincard' S = 
fincard' (fixed_points μ) + ∑' o in (orbits_not_singleton μ), fincard' o := sorry


end mygroup
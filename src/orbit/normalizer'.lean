import orbit.orbit_stabilizer
import subgroup.definitions
namespace mygroup

open classical function set mygroup.subgroup mygroup.group
variables {G : Type} [group G]

def normalizer' (H : subgroup G) := stabilizer (conjugation_action) H

lemma mem_normalizer'_def  {H : subgroup G} (x : G) :
  x ∈ normalizer' H ↔ {k : G | ∃ (h : G) (H : h ∈ H), k = x * h * x⁻¹} = H := 
subgroup.ext'_iff.symm

lemma mem_normalizer'_iff {H : subgroup G} (x : G):
  x ∈ normalizer' H ↔ ∀ k : G, k ∈ H ↔ x * k * x⁻¹ ∈ H := 
begin
  rw mem_normalizer'_def,
  split,
  { intros hx s,
    rw ext_iff at hx,
    specialize hx (x * s *x⁻¹) ,
    dsimp at hx,
    rw mem_coe' at hx,
    rw ← hx,
    split,
    { rintro hs, use [s, hs] },
    { rintro ⟨h, hh, hsx⟩,
      convert hh,
      apply mul_left_cancel x, 
      apply mul_right_cancel x⁻¹,
      assumption } },
    { intro hx,
      ext y,
      split,
      { rintro ⟨s, hs, rfl⟩, exact ( hx s ).1 hs},
      { intro hy,
        use x⁻¹ * y * x,
        split,
          { change y ∈ H at hy,
            convert (hx (x⁻¹ * y * x)).2 _,
            convert hy,
            simp [group.mul_assoc] },
          { simp [group.mul_assoc] } } }
end  


lemma normalizer'_eq_set_normalizer (H : subgroup G) : 
  (normalizer' H  : set G) = { g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H } := 
by { ext, rw [subgroup.mem_coe', mem_normalizer'_iff], refl }

lemma normalizer_eq_normalizer' (H : subgroup G) : 
  normalizer H.carrier = normalizer' H :=
begin
  apply subgroup.ext'_iff.1,
  change (normalizer H.carrier).carrier = normalizer' H,
  rw normalizer'_eq_set_normalizer, refl,
end


def set_of_lcosets (H : subgroup G) := { B | ∃ g : G, B = lcoset g H }
--Why is there a problem with the notation?
--Need to coerce lcoset_partition to a collection of sets?
--HOW TO WRITE h as an element of G in to_fun?


--#exit
def dumb_fun' (H : subgroup G) (g' : G) (lcoset g H : set_of_lcosets H) := lcoset (g' * g) H


def dumb_fun (H : subgroup G) (h : H) (lcoset g H : set_of_lcosets H) := lcoset (h.1 * g) H



def dumb_action (H : subgroup  G): laction G (set_of_lcosets H) := 
{ to_fun := λ (h : H) (lcoset g H) , lcoset (h *g)  H ,
  map_one' := _,--when g ∈ H
  map_assoc' := _ }

lemma index_normalizer_congr_index_modp [fintype G] 
  {p : ℕ} (hp: p.prime) (H : subgroup G) (h: is_p_subgroup H p) :
  index' (normalizer (H : set G)) H ≡ index H [MOD p] := sorry  
--I want to say that here H acts on the set of cosets X = G/H by φ : H × X → X, (h, gH) ↦ hgH. 
--Then the set of points fixed by the action of H is X^H = {gH ∈ X | hgH = gH ∀ h ∈ H}
--We want to show that hgH=gH ∀ h ∈ H ↔ g ∈ normalizer H. Hence |X^H|= |(normalizer H)/H|.
-- Applying the lemma card_set_congr_card_fixed_points_mod_prime 
--we show that |(normalizer H)/H| ≡ |G/H|[MOD p], i.e. index' (normalizer (H : set G)) H ≡ index H [MOD p] 


lemma normalizer_neq_subgroup [fintype G] 
  (H : subgroup G) {p : ℕ} (hp: p.prime) (h: is_p_subgroup H p) : 
  p ∣ index H → normalizer (H : set G) ≠ H := sorry
--We rewrite p ∣ (index' (normalizer (H : set G)) H) using the previous lemma.
--This implies (index' (normalizer (H : set G)) H) ≠ 1, and hence we get the conclusion.


theorem sylow_one_part1 [fintype G] 
  {p m n: ℕ} {hp : p.prime} {hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m} : 
  ∀ (i ≤ n), ∃ H : subgroup G, fincard' H = p ^ i := sorry
-- and want to write that each of these subgroups of cardinality p^i is normal 
-- in a subgroup of cardinality p^(i+1)

/-class sylow_p_subgroup (G : Type) [group G] [fintype G] (p : ℕ) extends p_subgroup G :=
(maximal: ⊥ )-/

--need to define is_sylow_p_subgroup

lemma conjugates_eq_cardinality (g : G) (H : subgroup G) : fincard' H = fincard' (conjugate_subgroup g H) := sorry 

/-def conjugate_isomorphic (g : G) (H : subgroup G): H ≅ conjugate_subgroup g H :=
{ to_fun := λ (h : H), g * h * g⁻¹,
  map_mul' := _,
  is_bijective := _ }-/


/-theorem sylow_two [fintype G]{p : ℕ} {hp : p.prime} (h₁ : is_sylow_p_subgroup H p)(h₂ : is_sylow_p_subgroup K p) : 
∃ (g : G), H = conjugate_subgroup g K  := sorry -/ -- need coercion from sylow p subgroup to subgroup
-- Consider the action of K on the set X of cosets of H in G μ: K × X → X, (y, xH) ↦ yxH. 
--Consider the points fixed by the action. Notice that since H is a Sylow p subgroup then p does not divide 
--fincard' X = index H, hence fincard'(fixed points μ ) ≠ 0. We then want to show that xH ∈ fixed_points μ 
--implies that the conjugate of K by x is a subgroup of H. Since conjugates are isomorphic they have the same cardinality.
--Hence x K x⁻¹ = H.


--Define the number of Sylow p-subgroups of G.
def number_sylow_p {p : ℕ} {hp : p.prime}: fincard' {K ∣ is_sylow_p_subgroup K p}

theorem sylow_three [fintype G]{p m n: ℕ} {hp : p.prime}{hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m}:
(number_sylow_p ≡ 1 [MOD p]) ∧ (number_sylow_p ∣ m) := sorry 

end mygroup
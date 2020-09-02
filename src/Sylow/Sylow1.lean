import orbit.orbit_stabilizer
import subgroup.definitions
import Sylow.cauchy
namespace mygroup
open classical function set mygroup.subgroup mygroup.group
variables {G : Type} [group G]



open mygroup.subgroup

-- Definition of p-group for finite groups, not using definition of order of 
-- an element explicitly
class p_group [fintype G] (p : ℕ) extends group G :=
(card_pow_p: ∃ n : ℕ , fincard' G = p^n)

--A p-subgroup is a subgroup of a group G which is itself a p-group
class p_subgroup (G : Type) [group G] [fintype G] (p : ℕ) extends subgroup G :=
(card_pow_p: ∃ n : ℕ , fincard' (carrier) = p^n)


def is_p_subgroup (H : subgroup G) (p : ℕ) : Prop := 
  ∃ n : ℕ , fincard' (H) = p ^ n 

def is_lcoset (H : subgroup G) (B : set G) : Prop := ∃ g : G, B = lcoset g H

def lcosets (H : subgroup G) := {B : set G // is_lcoset H B}

def dumb_fun' (H : subgroup G) (g' : G) (X : set G) : set G :=
  {t | ∃ x : G, x ∈ X ∧ t = g' * x}

def dumb_fun (H : subgroup G) (g' : G) (X : lcosets H) : lcosets H :=
⟨dumb_fun' H g' X.1, 
begin
  rcases X with ⟨g , ⟨w, rfl⟩⟩, 
  use (g' * w),
  unfold dumb_fun',
  ext, 
  split,
  { intro hx,
    rcases hx with ⟨hx_w, ⟨h, hh, rfl⟩, rfl⟩,
    use h,
    simpa [group.mul_assoc] 
  },
  { rintro ⟨h, hh, rfl⟩,
    use w * h,
    simpa [group.mul_assoc]    
  },
end⟩



def dumb_action (H : subgroup  G): laction G (lcosets H) := 
{ to_fun := dumb_fun H,
  map_one' := 
    begin 
        intro S,
        unfold dumb_fun,
        dsimp,
        unfold dumb_fun',
        simp
    end,  
  map_assoc' := 
    begin
        intros g h S,
        rcases S with ⟨_, g', rfl⟩,
        unfold dumb_fun,
        unfold dumb_fun',
        norm_num,
        ext1,
        norm_num,
        split,
        {   intro hx,
            rcases hx with ⟨_, ⟨t, ⟨s, ⟨hs, ht⟩⟩, rfl⟩, rfl⟩,
            use t,
            split,
            use [s, hs], exact ht,
            rw group.mul_assoc
        },
        {   intro hx,
            rcases hx with ⟨_, ⟨s, hs, rfl⟩, rfl⟩,
            split,    --why all the splits?
            split,
            split, 
            use [s, hs], 
            simp [group.mul_assoc]        
        }    
  end }

--Do I use this to show H is normal in its normalizer?
def normal_in_normalizer (H : subgroup G): normal (normalizer H.carrier) := sorry

lemma index_normalizer_congr_index_modp [fintype G] 
  {p : ℕ} (hp: p.prime) (H : subgroup G) (h: is_p_subgroup H p) :
  index' (normalizer (H : set G)) H ≡ index H [MOD p] := 
  begin
    --have claim: ∀ g : G, (g ⋆ H) ∈ fixed_points (dumb_action H) ↔ g ∈ normalizer H,
    --    {sorry},
    sorry  
  end    

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
  {p m n: ℕ} {hp : p.prime} {hn : n ≥ 1}{hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m} : 
  ∀ (i ≤ n), ∃ H : subgroup G, fincard' H = p ^ i := 
begin
  intros i hi,
have claim : ∃ H : subgroup G, fincard' H = p,
  { apply cauchy,
        exact hp,

        rw hG, refine dvd_mul_of_dvd_left _ m,
        refine (nat.dvd_prime_pow hp).mpr _,
        use 1, simpa [nat.pow_one],
  },
  induction i with i hi,   
  use ⊥ ,
  rw nat.pow_zero,
  exact fincard_bot,
  rw nat.succ_eq_add_one at *,  --don't I need strict inequality at hs?
  rw nat.pow_succ,

 -- cases claim with H hH,

  --Let H < G s.t. fincard' H = p ^i . Then p ∣ index H → p∣ index' normalizer H H
  sorry    
end    
/-theorem cauchy (G : Type) [group G] [fintype G] (p : ℕ) (hp : p.prime)
  (hpG : p ∣ fincard' G) : ∃ H : subgroup G, fincard' H = p := -/

-- and want to write that each of these subgroups of cardinality p^i is normal 
-- in a subgroup of cardinality p^(i+1)

def conjugate_iso (g : G) (H : subgroup G) : H ≅ conjugate_subgroup g H :=
{ to_fun := λ (h : H) , ⟨g * h * g⁻¹, begin use [h, h.2] end⟩,
  map_mul' := 
    begin
      intros x y,
      rw ← group.mul_one x,

       sorry     
    --  rw ← group.mul_left_inv g,     
    end    ,
  is_bijective := 
    begin
      split,
        {   intros x y hxy ,
            dsimp at *,
            cases y with y hy, 
            cases x with x hx, 
            sorry           
          },
        {   sorry}
    end     }


-- group iso -> equiv -> same cardinality
lemma conjugates_eq_cardinality (g : G) (H : subgroup G) :
  fincard' H = fincard' (conjugate_subgroup g H) := sorry 

def is_sylow_p_subgroup (K : subgroup G) {p : ℕ} (hp : p.prime) : Prop := sorry

theorem sylow_two [fintype G]{p : ℕ} {hp : p.prime} (H K : subgroup G) (h₁ : is_sylow_p_subgroup H hp)(h₂ : is_sylow_p_subgroup K hp) : 
∃ (g : G), H = conjugate_subgroup g K  := sorry  -- need coercion from sylow p subgroup to subgroup
-- Consider the action of K on the set X of cosets of H in G μ: K × X → X, (y, xH) ↦ yxH. 
--Consider the points fixed by the action. Notice that since H is a Sylow p subgroup then p does not divide 
--fincard' X = index H, hence fincard'(fixed points μ ) ≠ 0. We then want to show that xH ∈ fixed_points μ 
--implies that the conjugate of K by x is a subgroup of H. Since conjugates are isomorphic they have the same cardinality.
--Hence x K x⁻¹ = H.



--Define the number of Sylow p-subgroups of G. 
noncomputable def number_sylow_p (G : Type) [group G] {p : ℕ} (hp : p.prime) := fincard' {K : subgroup G // is_sylow_p_subgroup K hp}

theorem sylow_three_part1 [fintype G]{p m n: ℕ}{hp : p.prime}
  {hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m}:
number_sylow_p G hp ≡ 1 [MOD p] := sorry 
theorem sylow_three_part2 [fintype G]{p m n: ℕ} {hp : p.prime}{hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m}:
number_sylow_p G hp ∣ m := sorry 
--By Sylow 1 ∃ a Sylow p-subgroup P, so we set X = Sylp(G) = {Sylow p-groups in G}
--Then P acts on X by μ : P × X → X, (x, Q) ↦ xQx⁻¹ (this is what we defined conjugate_action to be)
--By card_set_congr_card_fixed_points_mod_prime we have
-- number_sylow_p = fincard' X ≡ fincard' (fixed points μ) [MOD p]. Want to show fincard' (fixed points μ) = 1.
--Let P ∈ fixed points μ and Q ∈ fixed points μ. Then P is a subgroup of normalizer Q
--Both P and Q are Sylow p-subgroups of normalizer Q, so ∃ x ∈ normalizer Q s.t. xQx⁻¹ = P (Sylow 2)
--By def of normalizer Q we have Q = P, so fixed_points μ = {P}, proving the first part of the theorem.end
--Now if P acts on X by conjugation ∃ ! orbit such that X = orbit G P (Sylow 2).
--By orbit-stabilizer number_sylow_p = (fincard' X) ∣ (fincard' G)=p^n *m which implies it divides m.

end mygroup
import subgroup.lagrange
import data.nat.modeq

noncomputable theory

namespace mygroup

open_locale classical

open set classical function

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

@[ext] lemma ext (μ1 μ2 : laction G S)
  (h : ∀ (g : G) (s : S), μ1.to_fun g s = μ2.to_fun g s) :
μ1 = μ2 :=
begin
  cases μ1, cases μ2, simp * at *,
  ext g s, apply h,
end

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
    { rw [←h, map_assoc, group.mul_left_inv, map_one] },
    { rw [h, map_assoc, group.mul_right_inv, map_one] }
end

end laction

/-- The orbit of some element of `s : S` is the image of the left action at `s` -/
def orbit (μ : laction G S) (s : S) : set S := 
  { m : S | ∃ g : G, m = g •[μ] s } 

namespace laction

@[simp]
lemma orbit_def {s : S} : orbit μ s = { m : S | ∃ g : G, m = g • s } := rfl

@[simp]
lemma mem_orbit {s t : S} : t ∈ orbit μ s ↔ ∃ g : G, t = g • s := 
by rw [orbit_def, mem_set_of_eq]

/-- An element of `G` is in its own orbit -/
lemma mem_orbit_refl (s : S) : s ∈ orbit μ s := ⟨1, (map_one μ s).symm⟩

/-- If `s₁ : S` is in `s₂ : S`'s orbit, then `s₂` is in `s₁`'s orbit -/
lemma mem_orbit_symm {s₁ s₂ : S} (h : s₁ ∈ orbit μ s₂) : s₂ ∈ orbit μ s₁ := 
let ⟨g, hg⟩ := h in ⟨g⁻¹, by rw [hg, map_assoc, group.mul_left_inv, map_one]⟩

/-- If s₁ ∈ [s₂] and s₂ ∈ [s₃] then s₁ ∈ [s₃] -/
lemma mem_orbit_trans {s₁ s₂ s₃ : S} 
  (hs₁ : s₁ ∈ orbit μ s₂) (hs₂ : s₂ ∈ orbit μ s₃) : s₁ ∈ orbit μ s₃ :=
begin
  cases hs₁ with g₁ hg₁,
  cases hs₂ with g₂ hg₂,
  refine ⟨g₁ * g₂, _⟩,
  rw [hg₁, hg₂, map_assoc]
end

/-- If two elements of `S` are in the same orbit then they are in eachothers orbit-/
lemma in_orbit_of_in_same_orbit {s₁ s₂ s₃ : S} 
  (hs₁ : s₁ ∈ orbit μ s₃) (hs₂ : s₂ ∈ orbit μ s₃) : s₁ ∈ orbit μ s₂ :=
begin
  cases hs₁ with g₁ hg₁,
  cases hs₂ with g₂ hg₂,
  refine ⟨g₁ * g₂⁻¹, _⟩,
  rw [hg₁, hg₂, map_assoc, group.mul_assoc, group.mul_left_inv, group.mul_one]
end

lemma in_orbit_of_inv' {s₁ s₂ : S} {g : G} (h : s₁ = g • s₂) : 
  s₂ = g⁻¹ • s₁ := by rw [h, map_assoc, group.mul_left_inv, map_one]

lemma eq_orbit {s₀ s₁ : S} (t : S) 
  (hs₁ : t ∈ orbit μ s₀) (hs₂ : t ∈ orbit μ s₁) : orbit μ s₀ = orbit μ s₁ :=
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

-- This will be used in one of the lemmas later
lemma nat.zero_or_one_of_le_one {n : ℕ} (hn : n ≤ 1) : n = 0 ∨ n = 1 := 
begin
  induction n, finish,
  rw nat.succ_le_iff at hn,
  change _ < 1 + 0 at hn,
  rw nat.lt_one_add_iff at hn,
  rw nat.le_zero_iff at hn,
  right, rw hn,
end

namespace laction

@[simp]
lemma mem_stabilizer (s : S) (g : G) : g ∈ stabilizer μ s ↔ g • s = s := iff.rfl

/-- If `H` is the conjugate of `K`, then `K` is the conjugate of `H` -/
lemma is_conjugate_symm {H K : subgroup G} (h : is_conjugate H K) :
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
  (hs₁ : s₁ ∈ orbit μ s₃) (hs₂ : s₂ ∈ orbit μ s₃) : 
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

def fixed_points (μ : laction G S) : set S := { s : S | ∀ g : G, g •[μ] s = s }

@[simp] lemma mem_fixed_points_iff (s : S) :
  s ∈ fixed_points μ ↔ ∀ (g : G) , g • s = s := iff.rfl

lemma mem_fixed_points_iff_stabilizer_univ (s : S) :
  s ∈ fixed_points μ ↔ stabilizer μ s = ⊤ :=
begin
  rw mem_fixed_points_iff,
  rw subgroup.eq_top_iff',
  apply forall_congr,
  intro a, refl
end

lemma orbit_eq_singleton {s : S} {μ : laction G S} (h : s ∈ fixed_points μ) : 
  orbit μ s = {s} := by ext x; simp * at *

lemma mem_fixed_points {s : S} {μ : laction G S} (h : orbit μ s = {s}) :
  s ∈ fixed_points μ := λ k, mem_singleton_iff.1 begin exact h ▸ ⟨k, rfl⟩ end

lemma orbit_eq_singleton_iff {s : S} {μ : laction G S} :
  orbit μ s = {s} ↔ s ∈ fixed_points μ := ⟨mem_fixed_points, orbit_eq_singleton⟩

lemma mem_fixed_points_iff_card_orbit_eq_one {s : S} {μ : laction G S}:
  s ∈ fixed_points μ ↔ fincard' (orbit μ s) = 1 :=
begin
  rw ← orbit_eq_singleton_iff,
  split; intro h,
    { simp [h] },
    { rw eq_singleton_iff_unique_mem,
      refine ⟨laction.mem_orbit_refl _, λ y hy, _⟩,
      rcases fincard.card_eq_one_iff_singleton.1 h with ⟨x, hx⟩, 
      rw hx at hy,
      rw [mem_singleton_iff.1 hy, ← mem_singleton_iff, ← hx],
      exact laction.mem_orbit_refl _ }
end

-- should now prove that for G acting on S, size of S = sum
-- of size of orbits.

/-- Orbits of an action -/
def orbits (μ : laction G S) := setoid.classes
  { r := λ (x y : S), x ∈ orbit μ y,
    iseqv := ⟨laction.mem_orbit_refl,
            λ x y, laction.mem_orbit_symm,
            λ x y z, laction.mem_orbit_trans⟩ }

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

lemma card_orbits_eq_one [fintype S] {s : set S} 
  (hs₀ : s ∈ orbits μ) (hs₁ : fincard' s ≤ 1) : fincard' s = 1 :=
begin
  cases nat.zero_or_one_of_le_one hs₁,
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

-- I don't think this is needed anymore
lemma pow_prime_eq_one_or_dvd_prime {p d n : ℕ} (hp: p.prime) (hd: d = p^n) : 
  d = 1 ∨ p ∣ d := 
begin
  cases n,
  left, rw hd, refl,
  right, simp [hd, nat.succ_eq_add_one, nat.pow_succ]
end

-- Are these names okay? Should I leave these lemmas here?
lemma card_orbit_div_pow_p [fintype S] [fintype G] (μ : laction G S)
  (p : ℕ) (hp : p.prime) (n : ℕ) (hG : fincard' G = p ^ n):
  ∀ s : S, fincard'( orbit μ s ) ∣ p^n :=
begin
  intro s, rw ← hG,
    use (fincard' (stabilizer μ s)),
    rw laction.orbit_stabilizer,
end  

lemma card_orbit_eq_one_or_dvd_p [fintype S] [fintype G] (μ : laction G S) 
  (p : ℕ) (hp : p.prime) (n : ℕ) (hG : fincard' G = p ^ n) : 
  ∀ (s : S), fincard' (orbit μ s) = 1 ∨ p ∣ fincard' (orbit μ s) :=
begin
  intro s,
  cases (card_orbit_div_pow_p μ p hp n hG) s with _ _,
  have h1: fincard' ↥(orbit μ s) ∣ p^n,
    { use w, exact h },
  rw nat.dvd_prime_pow hp at h1,
  rcases h1 with ⟨_ | a, _, ha⟩; rw ha,
    { rw nat.pow_zero, left, refl },
    { right, rw nat.pow_succ, use p ^ a, rw mul_comm }
end  

lemma card_set_congr_card_fixed_points_mod_prime [fintype S] [fintype G]
  (μ : laction G S) (p : ℕ) (hp : p.prime) (n : ℕ) (hG : fincard' G = p ^ n) :
  fincard' S ≡ fincard' (fixed_points μ) [MOD p] := 
begin
  rw card_set_eq_card_fixed_points_sum_card_orbits μ,
  refine nat.modeq.modeq_of_dvd _,
  suffices: ↑p ∣ ↑∑' (o : set S) in 
    ({ o ∈ orbits μ | 1 < fincard' o } : set (set S)), fincard' o,
    { simpa [sub_eq_add_neg] },
  norm_cast, apply fincard.finsum_divisible_by,
  rintro x h,
  rcases h with ⟨⟨s, hs⟩, hr⟩,
  change x = orbit μ s at hs,
  rw hs, cases card_orbit_eq_one_or_dvd_p μ p hp n hG s,
  rw [hs, h] at hr,
  linarith, assumption
end

-- Given a subset H of a group G, its conjugate is also a subgroup of G
def conjugate_subgroup [group G] (g : G) (H : subgroup G) :  subgroup G :=
{ carrier := { k| ∃ h ∈ H, k = g * h * g⁻¹ },
  one_mem' := ⟨(1 : G), H.one_mem, by rw [group.mul_one, group.mul_right_inv]⟩,
  mul_mem' := λ x y ⟨s, hs, h1⟩ ⟨t, ht, h2⟩, 
    ⟨s * t, H.mul_mem hs ht, by rw [h1, h2]; simp [group.mul_assoc]⟩,
  inv_mem' := λ x ⟨s, hs, hx⟩, ⟨s⁻¹, H.inv_mem hs, 
    group.inv_eq_of_mul_eq_one (by rw hx; simp [group.mul_assoc])⟩ }

lemma conjugate_is_conjugate (g : G) (H : subgroup G) : 
  is_conjugate H (conjugate_subgroup g H) :=
begin
  refine ⟨g⁻¹, _⟩, ext x,
  apply exists_congr,
  simp [conjugate_subgroup],
end

lemma mul_equiv_of_is_conjugate {H K : subgroup G} (e : is_conjugate H K) :
 H ≃* K :=
let ⟨g, hg⟩ := classical.indefinite_description _ e in
begin
  dsimp at hg,
  rw ext_iff at hg,
  change ∀ x : G, (∃ (h : G), _) ↔ x ∈ K at hg,
  exact 
  { to_fun := λ h, ⟨g⁻¹ * h * g, show _ ∈ K, 
      begin rw ←hg, use [h.1, h.2], refl end⟩,
    inv_fun := λ k, ⟨g * k.1 * g⁻¹, 
      begin 
        show _ ∈ H, cases k with k hk,
        rcases (hg k).2 hk with ⟨t, h1, h2⟩,
        convert h1, subst h2, simp [group.mul_assoc],
      end⟩,
    left_inv := λ ⟨_, _⟩, by simp [group.mul_assoc],
    right_inv := λ ⟨_, _⟩, by simp [group.mul_assoc],
    map_mul' := λ ⟨_, _⟩ ⟨_, _⟩, by ext; simp [group.mul_assoc] } 
end

def conjugation_action [group G]: laction G (subgroup G) :=
{ to_fun := λ (g : G) (H : subgroup G), conjugate_subgroup g H,
  map_one' := 
    begin
      intro H,
      unfold conjugate_subgroup,
      norm_num, ext, split,
      repeat { intro hx, exact hx },         
    end  ,
  map_assoc' := 
    begin
      intros s t H,
      ext, split, unfold conjugate_subgroup,
        { intro hx,
          rcases hx with ⟨h, ⟨⟨k, ⟨j, hj⟩⟩, h2⟩⟩, 
          rw hj at h2,
          suffices: x = s * t * k * (t⁻¹ * s⁻¹), tidy,
          rw [← group.mul_assoc, h2, group.mul_assoc],
          apply group.mul_eq_of_eq_inv_mul,
          symmetry,
          iterate 4 { rw ← group.mul_assoc },
          rw [group.mul_left_inv, group.one_mul] },
        { intro hx,
          rcases hx with ⟨h, ⟨hh, hj⟩⟩,
          suffices: x ∈ conjugate_subgroup s (conjugate_subgroup t H), tidy,
          rw [← group.mul_assoc, ← group.mul_assoc, group.mul_assoc],
          assumption },
    end }

end mygroup
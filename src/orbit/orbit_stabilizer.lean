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

-- notation M ` →ₗ[`:25 R:25 `] `:0 M₂:0 := linear_map R M M₂

notation g ` ★[ `:70 μ ` ] `:0 s:0 := μ.to_fun g s
local notation g ` ★ `:70  s:70  := μ.to_fun g s

namespace laction

-- APIs for left actions 

@[simp] lemma map_one (μ : laction G S) (s : S) : (1 ★[μ] s) = s := μ.map_one' _

lemma map_assoc (g h : G) (s : S) : g ★ (h ★ s) = g * h ★ s := 
  μ.map_assoc' _ _ _

-- The user should prove these two lemmas below

lemma laction_mul_inv_cancel {g h : G} {s : S} : 
  g ★ s = h ★ s ↔ s = (g⁻¹ * h) ★ s :=
begin
  split; intro hgh,
    { conv_lhs { rw ←map_one μ s }, 
      rw [←(group.mul_right_inv g⁻¹), ←map_assoc, 
          ←map_assoc, ←hgh, group.inv_inv] },
    { conv_lhs { rw [hgh, map_assoc, ←group.mul_assoc, 
                     group.mul_right_inv, group.one_mul] } }
end

lemma laction_mul_inv {g : G} {s t : S} : g ★ s = t ↔ s = g⁻¹ ★ t :=
begin
  split; intro h,
    rw [←h, map_assoc, group.mul_left_inv, map_one],
    rw [h, map_assoc, group.mul_right_inv, map_one]
end

end laction

/-- The orbit of some element of `s : S` is the image of the left action at `s` -/
def orbit (μ : laction G S) (s : S) : set S := 
  { m : S | ∃ g : G, m = g ★[μ] s } 

local notation `💫`:70 s:70 := orbit μ s

namespace laction

@[simp]
lemma orbit_def {s : S} : 💫 s = { m : S | ∃ g : G, m = g ★ s } := rfl

@[simp]
lemma mem_orbit {s t : S} : t ∈ 💫 s ↔ ∃ g : G, t = g ★ s := 
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

lemma in_orbit_of_inv' {s₁ s₂ : S} {g : G} (h : s₁ = g ★ s₂) : 
  s₂ = g⁻¹ ★ s₁ := by rw [h, map_assoc, group.mul_left_inv, map_one]

end laction

/-- The stabilizer of `s : S` is the subgroup which elements fixes `s` under the 
  left laction -/
def stabilizer (μ : laction G S) (s : S) : subgroup G := 
{ carrier := { g : G | (g ★[μ] s) = s },
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
lemma mem_stabilizer (s : S) (g : G) : g ∈ stabilizer μ s ↔ g ★ s = s := iff.rfl

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
         (show h ★ s₁ = s₁, by exact hh₀), hg, map_assoc, 
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
        { g : G | g ★ a = a } at hxy,
      rw [mem_set_of_eq, ←μ.3, ←(extract ⟨x, hx⟩).2, 
        @laction_mul_inv _ _ _ μ _ x a, group.inv_inv, ←(extract ⟨y, hy⟩).2] at hxy,
      simp only [hxy] },
    { rintro ⟨_, g, hg⟩, refine ⟨⟨g ★ a, g, rfl⟩, _⟩,
      rw [subtype.mk.inj_eq, hg, lagrange.lcoset_eq],
      show g⁻¹ * (extract ⟨μ.to_fun g a, _⟩).val ∈ { g : G | g ★ a = a },
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

end laction

end mygroup

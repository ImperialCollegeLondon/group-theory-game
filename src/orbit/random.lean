import group_theory.subgroup data.fintype.basic

noncomputable theory

open set classical
local attribute [instance] prop_decidable

namespace action

structure laction (G : Type*) [group G] (S : Type*) :=
(to_fun    : G → S → S) (map_one : ∀ s : S, to_fun 1 s = s)
(map_assoc : ∀ g h : G, ∀ s : S, to_fun g (to_fun h s) = to_fun (g * h) s)

variables {G : Type*} [group G] {S : Type*}
variables {α : Type*} {μ : laction G S}

/- Example of a left action -/
def natural_self_laction : laction G G := 
{ to_fun := λ g h, g * h,
  map_one := one_mul,
  map_assoc := λ _ _ _, (mul_assoc _ _ _).symm }

@[reducible] def orbit (μ : laction G S) (s : S) : set S := 
  { m : S | ∃ g : G, m = μ.1 g s } 

lemma self_mem_orbit (s : S) : s ∈ orbit μ s := ⟨1, (μ.2 s).symm⟩

structure partition (S : Type*) :=
(blocks : set (set S))
(nonempty : ∀ block ∈ blocks, block ≠ ∅)
(covers : univ = ⋃ (s ∈ blocks), s)
(disj   : ∀ s t ∈ blocks, s ∩ t ≠ ∅ → s = t)

lemma not_empty {S : set α} (h : S ≠ ∅) : ∃ s : α, s ∈ S := 
begin
  by_contra hs, push_neg at hs,
  exact (push_neg.not_eq _ _).1 h (set.eq_empty_iff_forall_not_mem.2 hs)
end

/- The orbits form a partition -/
def orbit_partition : partition S := 
{ blocks := { o : set S | ∃ s : S, o = orbit μ s },
  nonempty := λ B hB hemp, by { rcases hB with ⟨s, rfl⟩,
    exact (eq_empty_iff_forall_not_mem.1 hemp s) (self_mem_orbit s) },
  covers := ext $ λ x,
    ⟨ λ hx, mem_Union.2 ⟨orbit μ x, mem_Union.2 ⟨⟨x, rfl⟩, ⟨1, (μ.2 _).symm⟩⟩⟩, 
      λ hx, mem_univ x ⟩,
  disj := 
    begin
      rintros _ _ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩ hndisj,
      rcases not_empty hndisj with ⟨x, hxs, hxt⟩,
      ext y, split,
        all_goals { intro hy,
          cases hxs with g₁ hg₁, cases hxt with g₂ hg₂, cases hy with g hg },
        { have : μ.1 g₁⁻¹ (μ.1 g₁ s₁) = μ.1 g₁⁻¹ (μ.1 g₂ s₂),
            rwa [eq.trans hg₁.symm hg₂],
          rw [μ.3, μ.3, inv_mul_self _, μ.2] at this,
          refine ⟨g * (g₁⁻¹ * g₂), _⟩,
          rw [hg, ←μ.3, this] },
        { have : μ.1 g₂⁻¹ (μ.1 g₂ s₂) = μ.1 g₂⁻¹ (μ.1 g₁ s₁),
            rwa [eq.trans hg₁.symm hg₂],
          rw [μ.3, μ.3, inv_mul_self _, μ.2] at this,
          refine ⟨g * (g₂⁻¹ * g₁), _⟩,
          rw [hg, ←μ.3, this] }
    end }

/- The stabilizer of an action is a subgroup -/
@[reducible]
def stabilizer (μ : laction G S) (s : S) : subgroup G := 
{ carrier := { g : G | μ.1 g s = s },
  one_mem' := μ.2 _,
  mul_mem' := λ _ _ hg hh, by { rw mem_set_of_eq at *, rw [←μ.3, hh, hg] },
  inv_mem' := λ x hx, 
    begin
      rw mem_set_of_eq at *, 
      conv_lhs { rw ←hx },
      rw [μ.3, inv_mul_self _, μ.2] 
    end }

lemma in_orbit_of_in_same_orbit {s₁ s₂ s₃ : S} :
s₁ ∈ orbit μ s₃ ∧ s₂ ∈ orbit μ s₃ → s₁ ∈ orbit μ s₂ :=
begin
  rintro ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩,
  refine ⟨g₁ * g₂⁻¹, _⟩,
  rw [hg₁, hg₂, μ.3, mul_assoc, inv_mul_self, mul_one]
end

lemma in_orbit_of_inv {s₁ s₂ : S} {g : G} (h : s₁ = μ.1 g s₂) : 
  s₂ = μ.1 g⁻¹ s₁ := by rw [h, μ.3, inv_mul_self, μ.2]

@[reducible]
def is_conjugate (H K : subgroup G) := 
  ∃ g : G, {c | ∃ h ∈ H, c = g⁻¹ * h * g } = K

lemma conjugate_stabilizer_of_in_same_orbit {s₁ s₂ s₃ : S} 
  (h : s₁ ∈ orbit μ s₃ ∧ s₂ ∈ orbit μ s₃) : 
  is_conjugate (stabilizer μ s₁) (stabilizer μ s₂) :=
begin
  cases in_orbit_of_in_same_orbit h with g hg,
  refine ⟨g, _⟩,
  ext, split; intro hx,
    { show x ∈ (stabilizer μ s₂).carrier, dsimp,
      rcases hx with ⟨h, hh₀, hh₁⟩,
      rw [hh₁, ←μ.3, ←μ.3, ←hg, 
        (show μ.to_fun h s₁ = s₁, by exact hh₀), hg, μ.3, inv_mul_self, μ.2] },
    { change x ∈ (stabilizer μ s₂).carrier at hx, dsimp at hx,
      exact ⟨g * x * g⁻¹, show g * x * g⁻¹ ∈ (stabilizer μ s₁).carrier, by dsimp;
        rw [←μ.3, ←(in_orbit_of_inv hg), ←μ.3, hx, hg], by simp [mul_assoc]⟩ }
end

end action

namespace order

-- We need Lagrange's theorem for Orbit-Stabilizer theorem
-- In this section we will only consider finite groups

open fintype

variables {G : Type*} [group G] [fintype G] 
variables {H : subgroup G}

@[reducible]
def lcoset (g : G) (H : subgroup G) : set G :=
  { k : G | ∃ h ∈ H, k = g * h }
notation g ` • ` : 70 H : 70 := lcoset g H

lemma self_mem_coset (a : G) (H : subgroup G): a ∈ a • H := 
  ⟨1, H.one_mem, (mul_one a).symm⟩

/-- Two cosets aH, bH are equal if and only if b⁻¹a ∈ H -/
theorem lcoset_eq {a b : G} :
  a • H = b • H ↔ b⁻¹ * a ∈ H := 
begin
  split; intro h,
    { replace h : a ∈ b • H, rw ←h, exact self_mem_coset a H,
      rcases h with ⟨g, hg₀, hg₁⟩,
      rw hg₁, simp [hg₀] },
    { ext, split; intro hx,
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          exact ⟨b⁻¹ * a * g, H.mul_mem h hg₀, by simp [mul_assoc]⟩ },
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          refine ⟨a⁻¹ * b * g, H.mul_mem _ hg₀, by simp [mul_assoc]⟩,
          convert H.inv_mem h, simp } }
end

-- A corollary of this is aH = H iff a ∈ H 

/-- The coset of H, 1H is H -/
lemma lcoset_of_one : 1 • H = H :=
begin
  ext, split; intro hx,
    { rcases hx with ⟨h, hh₀, hh₁⟩,
      rwa [hh₁, one_mul] },
    { exact ⟨x, hx, (one_mul x).symm⟩ }
end

/-- A left coset gH equals H if and only if g ∈ H -/
theorem lcoset_of_mem {a : G} :
  a • H = H ↔ a ∈ H := by rw [←lcoset_of_one, lcoset_eq]; simp

-- Now we would like to prove that all lcosets have the same order

/-- The cardinality of all lcosets are equal -/
theorem card_of_lcoset_eq {a b : G} : card (a • H) = card (b • H) := sorry

end order

namespace action

variables {G : Type*} [group G]

-- Let's define the centralizer 

/- A group (left) acts on itself by conjugation -/
def conj_laction : laction G G := 
{ to_fun := λ g h, g * h * g⁻¹,
  map_one := by simp,
  map_assoc := λ g h k, by simp [mul_assoc] }

def centralizer (g : G) : subgroup G := stabilizer conj_laction g 

end action
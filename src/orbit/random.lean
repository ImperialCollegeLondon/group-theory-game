import group_theory.subgroup data.fintype.basic 
import tactic -- remove once library_search bug is fixed

noncomputable theory

open set classical
local attribute [instance] prop_decidable

structure partition (S : Type*) :=
(blocks : set (set S))
(nonempty : ∀ block ∈ blocks, block ≠ ∅)
(covers : univ = ⋃ (s ∈ blocks), s)
(disj   : ∀ s t ∈ blocks, s ∩ t ≠ ∅ → s = t)

private lemma not_empty {α} {S : set α} (h : S ≠ ∅) : ∃ s : α, s ∈ S := 
begin
  by_contra hs, push_neg at hs,
  exact (push_neg.not_eq _ _).1 h (set.eq_empty_iff_forall_not_mem.2 hs)
end

namespace action

structure laction (G : Type*) [group G] (S : Type*) :=
(to_fun    : G → S → S) (map_one : ∀ s : S, to_fun 1 s = s)
(map_assoc : ∀ g h : G, ∀ s : S, to_fun g (to_fun h s) = to_fun (g * h) s)

variables {G : Type*} [group G] {S : Type*}
variables {μ : laction G S}

-- Example of a left action - The natural left action of a group acting on itself
def natural_self_laction : laction G G := 
{ to_fun := λ g h, g * h,
  map_one := one_mul,
  map_assoc := λ _ _ _, (mul_assoc _ _ _).symm }

@[reducible] def orbit (μ : laction G S) (s : S) : set S := 
  { m : S | ∃ g : G, m = μ.1 g s } 

/-- An element of `G` is in its own orbit -/
lemma self_mem_orbit (s : S) : s ∈ orbit μ s := ⟨1, (μ.2 s).symm⟩

/-- The set of orbits of a set forms a partition -/
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

/- We define the stabilizer of an action is as a subgroup -/
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

-- Some lemmas about orbits that are useful 

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
  ∃ g : G, { c | ∃ h ∈ H, c = g⁻¹ * h * g } = K

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
      rw [hh₁, hk₁], simp [mul_assoc, hk₀] },
    { rw mem_set_of_eq,
      refine ⟨g⁻¹ * x * g, _, by simp [mul_assoc]⟩,
      show g⁻¹ * x * g ∈ (K : set G),
      rw ←hg, exact ⟨x, hx, rfl⟩ }
end

/-- If two elements are in the same orbit, then their stabilizers are conjugates -/
theorem conjugate_stabilizer_of_in_same_orbit {s₁ s₂ s₃ : S} 
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

-- We need Lagrange's theorem for Orbit-Stabilizer 

/- We will use the cardinality function `fintype.card` defined for fintypes.
While we will prove most theorems in this section for general groups, we will 
only consider finite groups when considering the cardinality of the group in 
question. This is reflected by the [fintype G] tag in theorems regarding 
cardinality. 

TODO : refactor the card stuff -/

open function fintype

variables {G : Type*} [group G]
variables {H : subgroup G}

@[reducible]
def lcoset (g : G) (H : subgroup G) : set G :=
  { k : G | ∃ h ∈ H, k = g * h }
notation g ` • ` : 70 H : 70 := lcoset g H

lemma self_mem_coset (a : G) (H : subgroup G): a ∈ a • H := 
  ⟨1, H.one_mem, (mul_one a).symm⟩

/-- Two cosets `a • H`, `b • H` are equal if and only if `b⁻¹ * a ∈ H` -/
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

-- A corollary of this is a • H = H iff a ∈ H 

/-- The coset of `H`, `1 • H` equals `H` -/
theorem lcoset_of_one : 1 • H = H :=
begin
  ext, split; intro hx,
    { rcases hx with ⟨h, hh₀, hh₁⟩,
      rwa [hh₁, one_mul] },
    { exact ⟨x, hx, (one_mul x).symm⟩ }
end

/-- A left coset `a • H` equals `H` if and only if `a ∈ H` -/
theorem lcoset_of_mem {a : G} :
  a • H = H ↔ a ∈ H := by rw [←lcoset_of_one, lcoset_eq]; simp

/-- Two left cosets `a • H` and `b • H` are equal if they are not disjoint -/
theorem lcoset_digj {a b c : G} (ha : c ∈ a • H) (hb : c ∈ b • H) : 
  a • H = b • H :=
begin
  rcases ha with ⟨g₀, hg₀, hca⟩,
  rcases hb with ⟨g₁, hg₁, hcb⟩,
  rw lcoset_eq, rw (show a = c * g₀⁻¹, by simp [hca, mul_assoc]),
  rw (show b⁻¹ = g₁ * c⁻¹, 
    by rw (show b = c * g₁⁻¹, by simp [hcb, mul_assoc]); simp),
  suffices : g₁ * g₀⁻¹ ∈ H, simp [mul_assoc, this],
  exact H.mul_mem hg₁ (H.inv_mem hg₀)
end

-- Now we would like to prove that all lcosets have the same order

private def aux_map (a : G) (H :subgroup G) : H → a • H := 
  λ h, ⟨a * h, h, h.2, rfl⟩

private lemma aux_map_biject {a : G} : bijective (aux_map a H) := 
begin
  split,
    { intros x y hxy,
      suffices : (x : G) = y, 
        { ext, assumption },
        { simp [aux_map] at hxy, assumption } },
    { rintro ⟨y, y_prop⟩, 
      rcases y_prop with ⟨h, hh₀, hh₁⟩,
      refine ⟨⟨h, hh₀⟩, by simp [aux_map, hh₁]⟩ }
end

/-- There is a bijection between `H` and its left cosets -/
theorem lcoset_equiv {a : G} : H ≃ a • H := 
equiv.of_bijective (aux_map a H) aux_map_biject

/-- The cardinality of `H` equals its left cosets-/
lemma eq_card_of_lcoset {a : G} [fintype G] : card H = card (a • H) := 
begin
  rw card_eq, by_contra h,
  exact not_nonempty_iff_imp_false.1 h lcoset_equiv
end

/-- The cardinality of all left cosets are equal -/
theorem card_of_lcoset_eq {a b : G} [fintype G] : 
  card (a • H) = card (b • H) := by iterate 2 { rw ←eq_card_of_lcoset }

/-- The left cosets of a subgroup `H` form a partition -/
def lcoset_partition (G : Type*) [group G] (H : subgroup G) : partition G := 
{ blocks := { B | ∃ g : G, B = g • H },
  nonempty := λ B hB, let ⟨g, hg⟩ := hB in 
    λ h, by rw [←(mem_empty_eq g), ←h, hg]; exact self_mem_coset g H,
  covers := ext $ λ x, 
    ⟨λ _, mem_Union.2 ⟨x • H, mem_Union.2 ⟨⟨x, rfl⟩, self_mem_coset x H⟩⟩, 
      λ _, mem_univ x⟩,
  disj := λ s t hs ht hndisj,
      let ⟨g₀, hg₀⟩ := hs in 
      let ⟨g₁, hg₁⟩ := ht in
      let ⟨k, hks, hkt⟩ := not_empty hndisj in
    begin
      rw [hg₀, hg₁], 
      rw hg₀ at hks, rw hg₁ at hkt, 
      exact lcoset_digj hks hkt,
    end }

-- Now we prove that the card of a set equals the sum of the card of blocks

private def aux_map' {α} [fintype α] (p : partition α) : 
α → ⋃ (b ∈ p.blocks), b :=  λ a, ⟨a, p.3 ▸ mem_univ _⟩

private lemma aux_map'_biject {α} [fintype α] (p : partition α) : 
  bijective (aux_map' p) := 
⟨λ _ _ _, by finish [aux_map'], λ ⟨y, y_prop⟩, ⟨y, by unfold aux_map'⟩⟩

lemma Union_blocks_equiv {α} [fintype α] (p : partition α) : 
  α ≃ ⋃ (b ∈ p.blocks), b :=
equiv.of_bijective (aux_map' p) (aux_map'_biject p)

/-- The cardinality of a fintype `α` equals the cardinality of its partition -/
theorem eq_card_of_partition {α} [fintype α] (p : partition α) : 
  card α = card ⋃ (b ∈ p.blocks), b :=
begin
  rw card_eq, by_contra h,
  refine not_nonempty_iff_imp_false.1 h (Union_blocks_equiv p)
end

theorem card_Union {α} [fintype α] (p : partition α) [h : finite p.1] :
card (⋃ (s ∈ h.to_finset), s) = h.to_finset.sum (λ s, card s) := 
begin
  sorry
end

theorem lagrange [fintype G] : 
  card G = card { c | ∃ g : G, c = g • H } * card H := 
begin
  rw eq_card_of_partition (lcoset_partition G H),
  /-
  We need :
  card (↥⋃ (b ∈ (lcoset_partition G H).blocks), b) = ...(1)
  ∑ (b ∈ (lcoset_partition G H).blocks), card b     = ...(2)
  card ↥{c : set G | ∃ (g : G), c = g • H} * card ↥H  ...(3)
  -/
  sorry
end

end order

namespace action

variables {G : Type*} [group G]

-- Let's define the centralizer 

/-- A group (left) acts on itself by conjugation -/
def conj_laction : laction G G := 
{ to_fun := λ g h, g * h * g⁻¹,
  map_one := by simp,
  map_assoc := λ g h k, by simp [mul_assoc] }

/-- The centralizer of `g` is the stabilizer of `g` with the conjugate action -/
@[reducible] def centralizer (g : G) : subgroup G := stabilizer conj_laction g 

/-- Elements of the centralizer of `g : G` commutes with `g` -/
theorem comm_of_mem_centralizer {g h : G} (hc : h ∈ centralizer g) : 
  g * h = h * g := 
begin
  change h * g * h⁻¹ = g at hc,
  conv_lhs { rw [←hc] }, simp
end

-- The conjugate class of `g` is the orbit of `g` with the conjugate action 

end action
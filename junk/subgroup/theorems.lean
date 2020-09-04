import subgroup.definitions group.group_powers
import for_mathlib.finsum -- breaks many things

noncomputable theory

/-
An API for subgroups

Mathematician-friendly

Let G be a group. The type of subgroups of G is `subgroup G`. 
In other words, if `H : subgroup G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min (and even sup and inf). 
-/

-- This entire project takes place in the `mygroup` namespace
namespace mygroup

variables {G : Type} [group G]

namespace lagrange

variables {H : subgroup G}

lemma self_mem_coset (a : G) (H : subgroup G): a ∈ a ⋆ H := 
  ⟨1, H.one_mem, (group.mul_one a).symm⟩

/-- Two cosets `a ⋆ H`, `b ⋆ H` are equal if and only if `b⁻¹ * a ∈ H` -/
theorem lcoset_eq {a b : G} :
  a ⋆ H = b ⋆ H ↔ b⁻¹ * a ∈ H := 
begin
  split; intro h,
    { replace h : a ∈ b ⋆ H, rw ←h, exact self_mem_coset a H,
      rcases h with ⟨g, hg₀, hg₁⟩,
      rw hg₁, simp [←group.mul_assoc, hg₀] },
    { ext, split; intro hx,
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          exact ⟨b⁻¹ * a * g, H.mul_mem h hg₀, by simp [←group.mul_assoc]⟩ },
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          refine ⟨a⁻¹ * b * g, H.mul_mem _ hg₀, by simp [←group.mul_assoc]⟩,
          convert H.inv_mem h, simp } }
end

-- A corollary of this is a ⋆ H = H iff a ∈ H 

/-- The coset of `H`, `1 ⋆ H` equals `H` -/
theorem lcoset_of_one : 1 ⋆ H = H :=
begin
  ext, split; intro hx,
    { rcases hx with ⟨h, hh₀, hh₁⟩,
      rwa [hh₁, group.one_mul] },
    { exact ⟨x, hx, (group.one_mul x).symm⟩ }
end

/-- A left coset `a ⋆ H` equals `H` if and only if `a ∈ H` -/
theorem lcoset_of_mem {a : G} :
  a ⋆ H = H ↔ a ∈ H := by rw [←lcoset_of_one, lcoset_eq]; simp 

/-- Two left cosets `a ⋆ H` and `b ⋆ H` are equal if they are not disjoint -/
theorem lcoset_digj {a b c : G} (ha : c ∈ a ⋆ H) (hb : c ∈ b ⋆ H) : 
  a ⋆ H = b ⋆ H :=
begin
  rcases ha with ⟨g₀, hg₀, hca⟩,
  rcases hb with ⟨g₁, hg₁, hcb⟩,
  rw lcoset_eq, rw (show a = c * g₀⁻¹, by simp [hca, group.mul_assoc]),
  rw (show b⁻¹ = g₁ * c⁻¹, 
    by rw (show b = c * g₁⁻¹, by simp [hcb, group.mul_assoc]); simp),
  suffices : g₁ * g₀⁻¹ ∈ H, 
    { rw [group.mul_assoc, ←@group.mul_assoc _ _ c⁻¹],
      simp [this] },
  exact H.mul_mem hg₁ (H.inv_mem hg₀)
end

-- Now we would like to prove that all lcosets have the same order

open function

private def aux_map (a : G) (H : subgroup G) : H → a ⋆ H := 
  λ h, ⟨a * h, h, h.2, rfl⟩

private lemma aux_map_biject {a : G} : bijective $ aux_map a H := 
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
theorem lcoset_equiv {a : G} : H ≃ a ⋆ H := 
equiv.of_bijective (aux_map a H) aux_map_biject

-- We are going to use fincard which maps a fintype to its fintype.card 
-- and maps to 0 otherwise

open fincard

/-- The cardinality of `H` equals its left cosets-/
lemma eq_card_of_lcoset {a : G} : fincard H = fincard (a ⋆ H) := 
  fincard.of_equiv lcoset_equiv

/-- The cardinality of all left cosets are equal -/
theorem card_of_lcoset_eq {a b : G} : 
  fincard (a ⋆ H) = fincard (b ⋆ H) := by iterate 2 { rw ←eq_card_of_lcoset }

-- The rest of the proof will requires quotient

end lagrange

namespace normal

lemma mem_normal {x} {N : normal G} : 
  x ∈ N ↔ ∃ (g : G) (n ∈ N), x = g * n * g⁻¹ :=
begin
  split; intro h, 
    { exact ⟨1, x, h, by simp⟩ },
    { rcases h with ⟨g, n, hn, rfl⟩,
      exact conj_mem _ _ hn _ }
end

lemma mem_normal' {x} {N : normal G} : 
  x ∈ N ↔ ∃ (g : G) (n ∈ N), x = g⁻¹ * n * g :=
begin
  rw mem_normal,
  split; rintro ⟨g, n, hn, rfl⟩;
    { exact ⟨g⁻¹, n, hn, by simp⟩ }
end

-- Some equivalent definitions for normal groups from wikipedia

open subgroup 

-- Any two elements commute regarding the normal subgroup membership relation
lemma comm_mem_of_normal {K : normal G} 
  {g k : G} (h : g * k ∈ K) : k * g ∈ K :=
begin
  suffices : k * (g * k) * k⁻¹ ∈ K,
    { simp [group.mul_assoc] at this, assumption },
  refine normal.conj_mem _ _ h _
end

def normal_of_mem_comm {K : subgroup G} 
  (h : ∀ g k : G, g * k ∈ K → k * g ∈ K) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    suffices : g * (n * g⁻¹) ∈ K,
      { rwa ←group.mul_assoc at this },
    refine h _ _ _, simpa [group.mul_assoc]
  end, .. K } -- The .. tells Lean that we use K for the unfilled fields

-- If K is a normal subgroup of the group G, then the sets of left and right 
-- cosets of K in the G coincide
lemma nomal_coset_eq {K : normal G} : 
  ∀ g : G, g ⋆ (K : subgroup G) = (K : subgroup G) ⋆ g :=
begin
  -- dsimp, 
  -- Without the dsimp it displays weridly,
  -- dsimp not required if we write out right_coset g K however?
  intros g,
  ext, split; intro hx,
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g, _⟩,
      simp [group.mul_assoc] },
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g⁻¹, _⟩,
      simp [←group.mul_assoc] }
end

def normal_of_coset_eq {K : subgroup G} 
  (h : ∀ g : G, g ⋆ K = K ⋆ g) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    have : ∃ s ∈ K ⋆ g, s = g * n,
      { refine ⟨g * n, _, rfl⟩,
        rw ←h, exact ⟨n, hn, rfl⟩ },
    rcases this with ⟨s, ⟨l, hl₁, hl₂⟩, hs₂⟩,
    rw [←hs₂, hl₂],
    simpa [group.mul_assoc]
  end, .. K}

-- If K is normal then if x ∈ g K and y ∈ h K then x * y ∈ (g * h) K
lemma prod_in_coset_of_normal {K : normal G} {x y g h : G} 
  (hx : x ∈ g ⋆ K) (hy : y ∈ h ⋆ K) : x * y ∈ (g * h) ⋆ K :=
begin
  rcases hx with ⟨k₀, hx₁, rfl⟩,
  rcases hy with ⟨k₁, hy₁, rfl⟩,
  refine ⟨h⁻¹ * k₀ * h * k₁, _, _⟩,
    { refine K.1.3 _ hy₁, 
      convert K.2 _ hx₁ _, exact (group.inv_inv _).symm },
    { iterate 2 { rw group.mul_assoc },
      rw group.mul_left_cancel_iff g _ _,
      simp [←group.mul_assoc] }
end

def normal_of_prod_in_coset {K : subgroup G} 
  (h : ∀ x y g h : G, x ∈ g ⋆ K → y ∈ h ⋆ K → x * y ∈ (g * h) ⋆ K) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    rcases h (g * n) (g⁻¹ * n) g g⁻¹ 
      ⟨n, hn, rfl⟩ ⟨n, hn, rfl⟩ with ⟨m, hm₀, hm₁⟩,
    rw [←group.mul_right_cancel_iff n⁻¹,
        group.mul_assoc, group.mul_assoc, group.mul_assoc] at hm₁,
    suffices : g * n * g⁻¹ = m * n⁻¹, 
      rw this, exact K.mul_mem hm₀ (K.inv_mem hn),
    simp [←group.mul_assoc] at hm₁; assumption
  end, .. K }

end normal

end mygroup
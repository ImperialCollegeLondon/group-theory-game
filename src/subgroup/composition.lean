import subgroup.torsion

open_locale classical

namespace mygroup

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

/-- A group is nontrivial if and only if it top is not equal to its bot -/
def group.nontrivial (G : Type) [group G] : Prop := (⊥ : subgroup G) ≠ ⊤ 

@[simp] lemma group.nontrivial_def {G : Type} [group G] :
  group.nontrivial G ↔ (⊥ : subgroup G) ≠ ⊤ := iff.rfl

-- Some lemmas about pushing top and bot over isomorphisms
lemma subgroup.iso_bot_eq_bot {G H : Type} [group G] [group H] 
  (φ : G ≅ H) : subgroup.map φ.1 (⊥ : subgroup G) = (⊥ : subgroup H) := 
begin
  ext, rw [mem_map, mem_bot_iff],
  split, 
    { rintro ⟨_, hx, rfl⟩,
      rw mem_bot_iff at hx,
      subst hx,
      exact map_one _ },
    { rintro rfl,
      exact ⟨1, mem_bot_iff.2 rfl, map_one _⟩ }
end

/-- Everything is a member of top -/
lemma subgroup.mem_top {G : Type} [group G] (g : G) : g ∈ (⊤ : subgroup G) :=
begin
  change g ∈ ((⊤ : subgroup G) : set G),
  rw ← singleton_subset_iff,
  change {g} ≤ ((⊤ : subgroup G) : set G),
  rw ← subgroup.closure_le, simp,
end

lemma subgroup.iso_top_eq_top {G H : Type} [group G] [group H] 
  (φ : G ≅ H) : subgroup.map φ.1 (⊤ : subgroup G) = (⊤ : subgroup H) := 
begin
  ext, split; intro,
    { exact subgroup.mem_top _ },
    { rw mem_map,
      rcases φ.2.2 x with ⟨x, rfl⟩,
      refine ⟨x, subgroup.mem_top _, rfl⟩ }
end

/-- Nontrivial is a group property, that is it translates over group isomorphisms -/
lemma subgroup.nontrivial_of_iso_nontrivial {G H : Type} [group G] [group H] 
  (φ : G ≅ H) : group.nontrivial G → group.nontrivial H :=
begin
  intros hG h,
  apply hG, 
  rw [← subgroup.iso_top_eq_top (iso_symm φ),
      ← subgroup.iso_bot_eq_bot (iso_symm φ), h],
end

namespace normal

variables {G : Type} [group G]

-- def subgroup.le_hom {A B : subgroup G} (hAB : A ≤ B) : A →* B :=
--   monoid_hom.mk' (λ a, ⟨a.1, hAB a.2⟩) (λ _ _, rfl)

-- def subgroup.normal_pair {A B : subgroup G} (hAB : A ≤ B) : Prop :=
--   (monoid_hom.range (subgroup.le_hom hAB)).normal

-- @[simp] lemma subgroup.normal_pair_def {A B : subgroup G} (hAB : A ≤ B) :
--   subgroup.normal_pair hAB ↔ (monoid_hom.range (subgroup.le_hom hAB)).normal := iff.rfl

-- def subgroup.normal_pair' (A B : subgroup G): Prop :=
--   (monoid_hom.range (subgroup.le_hom (show A ⊓ B ≤ B, by exact inf_le_right))).normal

-- instance : has_top $ normal G := 
-- ⟨ { carrier := univ,
--     one_mem' := mem_univ _,
--     mul_mem' := λ _ _ _ _, mem_univ _,
--     inv_mem' := λ _ _, mem_univ _,
--     conj_mem' := λ _ _ _, mem_univ _ } ⟩

/-- The normal subgroup of a normal subgroup induced by a smaller normal 
  subgroup through the inclusion map -/
def normal.𝒾 {G : Type} [group G] {A B : normal G} (hle : A ≤ B) : normal B :=
{ carrier := { b | b.1 ∈ A },
  one_mem' := A.one_mem',
  mul_mem' := λ _ _ ha hb, A.mul_mem' ha hb,
  inv_mem' := λ _ h, A.inv_mem' h,
  conj_mem' := λ _ h _, A.conj_mem' _ h _ }

lemma normal.mem_𝒾 {G : Type} [group G] {A B : normal G} (hle : A ≤ B) 
  {g : G} (hg : g ∈ B) : (⟨g, hg⟩ : B) ∈ normal.𝒾 hle ↔ g ∈ A := iff.rfl

lemma normal.inv_𝒾 {G : Type} [group G] {A B : normal G} (hle : A ≤ B) 
  {g : G} (hg : g ∈ B) : (⟨g, hg⟩⁻¹ : B) = ⟨g⁻¹, B.inv_mem' hg⟩ := rfl

lemma normal.mul_𝒾 {G : Type} [group G] {A B : normal G} (hle : A ≤ B) 
  {g h : G} (hg : g ∈ B) (hh : h ∈ B) : 
  (⟨g, hg⟩ : B) * (⟨h, hh⟩ : B) = ⟨g * h, B.mul_mem' hg hh⟩ := rfl

attribute [simp] normal.mem_𝒾 normal.inv_𝒾 normal.mul_𝒾

variables (H : subgroup G) (N : normal G)

/-- A group is simple if and only if it is nontrivial and all its normal subgroups 
  are either top or bot -/
def is_simple (G : Type) [group G] :=
  group.nontrivial G ∧ ∀ N : normal G, N = ⊥ ∨ N = ⊤

@[simp] lemma is_simple_def (G : Type) [group G] : is_simple G ↔ 
  group.nontrivial G ∧ ∀ N : normal G, N = ⊥ ∨ N = ⊤ := iff.rfl

def chain_prop (A B : normal G) : Prop :=
  ∃ (hle : A ≤ B), is_simple $ B /ₘ (normal.𝒾 hle)

@[simp] lemma chain_prop_def {A B : normal G} :
  chain_prop A B ↔ 
  ∃ (hle : A ≤ B), is_simple $ B /ₘ (normal.𝒾 hle) := iff.rfl

instance normal.inhabited : inhabited $ normal G := ⟨ ⊥ ⟩

/-- Chain is a nonempty list of normal subgroups such that subsequent subgroups 
  satisfies `chain_prop`, and furthermore, it begins with bot and ends with top -/
structure chain (G : Type) [group G] :=
(carrier    : list (normal G))
(nonempty   : carrier ≠ list.nil)
(chain_prop : carrier.chain' chain_prop)
(chain_head : carrier.head = ⊥)
(chain_last : carrier.last nonempty = ⊤)

/-- A normal subgroup is maximal if and only if the quotient group by it is 
  simple -/
def is_maximal {N : normal G} (hN : N ≠ ⊤) : Prop := is_simple (G /ₘ N)

@[simp] lemma is_maximal_def {N : normal G} (hN : N ≠ ⊤) : 
  is_maximal hN ↔ is_simple (G /ₘ N) := iff.rfl

-- If N < M, then by the correspondence theorem, there is a proper normal 
-- subgroup in G / N which contradicts the is_simple hypothesis

/-- There is no proper subgroup containing a maximal subgroup -/
theorem maximal_is_max {N : normal G} (hproper : N ≠ ⊤) (h : is_maximal hproper) : 
  ∀ M : normal G, N < M → M = ⊤ :=
begin
  intros M hM,
  rw [is_maximal_def, is_simple_def] at h,
  rcases h with ⟨h₁, h₂⟩,
  cases h₂ ((normal_of_quotient_order_iso N).to_equiv ⟨M, le_of_lt hM⟩),
    { exfalso, refine not_le_of_lt hM _,
      change (⟨M, le_of_lt hM⟩ : { H // N ≤ H }) ≤ ⟨N, le_refl _⟩, 
      rw [(normal_of_quotient_order_iso N).ord', h],
      exact bot_le },
    { rw eq_top_iff,
      change (⟨⊤, le_top⟩ : { H // N ≤ H }) ≤ ⟨M, le_of_lt hM⟩, 
      rw [(normal_of_quotient_order_iso N).ord', h],
      exact le_top }
end

/-- An alternative version of `maximal_is_max` that requires `≤` instead of `<` -/
theorem maximal_is_max' {N : normal G} (hproper : N ≠ ⊤) (h : is_maximal hproper) : 
  ∀ M : normal G, N ≤ M → M = N ∨ M = ⊤ := 
begin
  intros M hM,
  rcases le_iff_lt_or_eq.1 hM with hlt | rfl,
    { exact or.inr (maximal_is_max hproper h _ hlt) },
    { exact or.inl rfl }
end

/-- Everything is in top -/
lemma mem_top {G : Type} [group G] (g : G) : g ∈ (⊤ : normal G) :=
begin
  rw [← mem_carrier, ← singleton_subset_iff],
  change {g} ≤ ((⊤ : normal G) : set G),
  rw ← normal.closure_le, simp,
end

def top_div_bot_iso : 
  G ≅ (⊤ : normal G) /ₘ (@normal.𝒾 _ _ ⊥ (⊤ : normal G) le_top) :=
{ to_fun := λ g, quotient.mk (@normal.𝒾 _ _ ⊥ (⊤ : normal G) le_top) 
    (⟨g, mem_top _⟩ : (⊤ : normal G)),
  map_mul' := by tidy,
  is_bijective := 
    begin
      refine ⟨_, by tidy⟩,
      intros x₁ x₂ hx, dsimp at hx,
      rw [← coe_eq_mk, ← coe_eq_mk, mk_eq'] at hx,
      rw @normal.inv_𝒾 _ _ (⊥ : normal G) _ bot_le at hx,
      erw @normal.mul_𝒾 _ _ (⊥ : normal G) _ bot_le at hx,
      erw [normal.mem_𝒾, mem_bot_iff] at hx,
      rw ← group.inv_eq_of_mul_eq_one hx,
      exact group.inv_inv _,
    end }

def to_top : G →* (⊤ : normal G) := ⟨λ g, ⟨g, mem_top _⟩, by tidy⟩
def to_top_iso : G ≅ (⊤ : normal G) := ⟨to_top, by tidy⟩

def trivial_chain (h : is_simple G) : chain G := 
{ carrier := [⊥, ⊤],
  nonempty := by simp,
  chain_prop := 
    begin
      simp, 
      refine ⟨subgroup.nontrivial_of_iso_nontrivial (top_div_bot_iso) h.1, λ N, _⟩,
      rcases h with ⟨h₁, h₂⟩,
      cases h₂ (comap to_top_iso.1 (normal.comap (quotient.mk _) N)) with h h,
        { left, rw eq_bot_iff at h ⊢,
          intros x hx,
          rcases exists_mk x with ⟨y, rfl⟩,
          rcases to_top_iso.2.2 y with ⟨x, rfl⟩,
          erw [mem_bot_iff, ← coe_one, mk_eq', group.one_inv, group.one_mul],
          change to_top_iso.1 x ∈ _,
          rw ← mem_comap, convert one_mem _, rw ← mem_bot_iff,
          apply h, erw [mem_comap, mem_comap], exact hx },
        { right, rw eq_top_iff at h ⊢,
          intros x hx,
          rcases exists_mk x with ⟨y, rfl⟩,
          rcases to_top_iso.2.2 y with ⟨x, rfl⟩,
          erw [coe_eq_mk, ← mem_comap, ← mem_comap],
          refine h (mem_top _) }
    end,
  chain_head := by simp,
  chain_last := by simp }

-- example [fintype G] : ∀ (n = fintype.card G), ∃ c : chain G, true :=
-- begin
--   intro n, apply nat.strong_induction_on n,
--   rintros k hk₁ rfl,
--   by_cases is_simple G,
--     sorry,
--     sorry
-- end

-- instance [fintype G] : inhabited $ chain G := ⟨ sorry ⟩

end normal

end mygroup
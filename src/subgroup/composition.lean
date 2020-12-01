import subgroup.torsion

open_locale classical

namespace mygroup

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

/-- A group is nontrivial if and only if it top is not equal to its bot -/
def group.nontrivial (G : Type) [group G] : Prop := (⊥ : subgroup G) ≠ ⊤ 

@[simp] lemma group.nontrivial_def {G : Type} [group G] :
  group.nontrivial G ↔ (⊥ : subgroup G) ≠ ⊤ := iff.rfl

-- Some lemmas about pushing top and bot over isomorphisms
lemma subgroup.map_bot_eq_bot {G H : Type} [group G] [group H] 
  (φ : G →* H) : subgroup.map φ (⊥ : subgroup G) = (⊥ : subgroup H) := 
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

lemma subgroup.map_top_eq_top {G H : Type} [group G] [group H] 
  (φ : G →* H) (hφ : surjective φ) : 
  subgroup.map φ (⊤ : subgroup G) = (⊤ : subgroup H) := 
begin
  ext, split; intro,
    { exact subgroup.mem_top _ },
    { rw mem_map,
      rcases hφ x with ⟨x, rfl⟩,
      refine ⟨x, subgroup.mem_top _, rfl⟩ }
end

/-- Nontrivial is a group property, that is it translates over group isomorphisms -/
lemma subgroup.nontrivial_of_iso_nontrivial {G H : Type} [group G] [group H] 
  (φ : G ≅ H) : group.nontrivial G → group.nontrivial H :=
begin
  intros hG h,
  apply hG, 
  rw [← subgroup.map_top_eq_top (iso_symm φ).1 (iso_symm φ).2.2,
      ← subgroup.map_bot_eq_bot (iso_symm φ).1, h],
end

/-- Everything is in top -/
lemma normal.mem_top {G : Type} [group G] (g : G) : g ∈ (⊤ : normal G) :=
begin
  rw [← normal.mem_carrier, ← singleton_subset_iff],
  change {g} ≤ ((⊤ : normal G) : set G),
  rw ← normal.closure_le, simp,
end

namespace composition

variables {G : Type} [group G]

-- def subgroup.le_hom {A B : subgroup G} (hAB : A ≤ B) : A →* B :=
--   monoid_hom.mk' (λ a, ⟨a.1, hAB a.2⟩) (λ _ _, rfl)

-- def subgroup.normal_pair {A B : subgroup G} (hAB : A ≤ B) : Prop :=
--   (monoid_hom.range (subgroup.le_hom hAB)).normal

-- @[simp] lemma subgroup.normal_pair_def {A B : subgroup G} (hAB : A ≤ B) :
--   subgroup.normal_pair hAB ↔ (monoid_hom.range (subgroup.le_hom hAB)).normal := iff.rfl

-- def subgroup.normal_pair' (A B : subgroup G): Prop :=
--   (monoid_hom.range (subgroup.le_hom (show A ⊓ B ≤ B, by exact inf_le_right))).normal

variables (H : subgroup G) (N : normal G)

/-- A group is simple if and only if it is nontrivial and all its normal subgroups 
  are either top or bot -/
def is_simple (G : Type) [group G] :=
  group.nontrivial G ∧ ∀ N : normal G, N = ⊥ ∨ N = ⊤

@[simp] lemma is_simple_def (G : Type) [group G] : is_simple G ↔ 
  group.nontrivial G ∧ ∀ N : normal G, N = ⊥ ∨ N = ⊤ := iff.rfl

lemma comap_eq_bot {G H : Type} [group G] [group H] {φ : G →* H} {N : normal H}
  (h : normal.comap φ N = (⊥ : normal G)) (hsur : surjective φ) : N = ⊥ :=
begin
  rw eq_bot_iff at h ⊢,
  intros n hn, erw normal.mem_carrier at hn ⊢,
  rcases hsur n with ⟨x, rfl⟩,
  rw ← normal.mem_comap at hn,
  rw [normal.mem_bot_iff.1 (h hn), map_one],
  exact (⊥ : normal H).one_mem'
end

lemma comap_eq_top {G H : Type} [group G] [group H] {φ : G →* H} {N : normal H}
  (h : normal.comap φ N = (⊤ : normal G)) (hsur : surjective φ) : N = ⊤ :=
begin
  rw eq_top_iff at h ⊢,
  intros n _, erw normal.mem_carrier,
  rcases hsur n with ⟨x, rfl⟩,
  exact(normal.mem_comap _).1 (h (normal.mem_top x))
end

/-- `is_simple` is a group property, that is, it translates over group 
  isomorphisms -/
lemma is_simple_of_iso {G H : Type} [group G] [group H] 
  (φ : G ≅ H) : is_simple G → is_simple H :=
begin
  refine λ hG, ⟨subgroup.nontrivial_of_iso_nontrivial φ hG.1, _⟩,
  intro N, rcases hG.2 (normal.comap φ.1 N) with hN | hN,
    { left, exact comap_eq_bot hN φ.2.2 },
    { right, exact comap_eq_top hN φ.2.2 }
end

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

def is_conj_mem (A B : subgroup G) : Prop := ∀ a ∈ A, ∀ g ∈ B, g * a * g⁻¹ ∈ A

@[simp] lemma is_conj_mem_def (A B : subgroup G) :
  is_conj_mem A B ↔ ∀ a ∈ A, ∀ g ∈ B, g * a * g⁻¹ ∈ A := iff.rfl

def normal.𝒾 {G : Type} [group G] {A B : subgroup G} (hle : A ≤ B) 
  (h : is_conj_mem A B) : normal B :=
{ carrier := { a | a.1 ∈ A },
  one_mem' := A.one_mem',
  mul_mem' := λ _ _ ha hb, A.mul_mem' ha hb,
  inv_mem' := λ _ h, A.inv_mem' h,
  conj_mem' := λ _ hs x, h _ hs _ x.2 }

lemma normal.mem_𝒾 {G : Type} [group G] {A B : subgroup G} (hle : A ≤ B) 
  (h : is_conj_mem A B) {g : G} (hg : g ∈ B) : 
  (⟨g, hg⟩ : B) ∈ normal.𝒾 hle h ↔ g ∈ A := iff.rfl

lemma normal.inclusion_inv {G : Type} [group G] {A B : subgroup G} (hle : A ≤ B) 
  {g : G} (hg : g ∈ B) : (⟨g, hg⟩⁻¹ : B) = ⟨g⁻¹, B.inv_mem' hg⟩ := rfl

lemma normal.inclusion_mul {G : Type} [group G] {A B : subgroup G} (hle : A ≤ B) 
  {g h : G} (hg : g ∈ B) (hh : h ∈ B) : 
  (⟨g, hg⟩ : B) * (⟨h, hh⟩ : B) = ⟨g * h, B.mul_mem' hg hh⟩ := rfl

attribute [simp] normal.mem_𝒾 normal.inclusion_inv normal.inclusion_mul

-- `chain_prop A B` means `∀ a ∈ A, g ∈ B, g * a * g⁻¹ ∈ A` 
def chain_prop (A B : subgroup G) : Prop := 
  ∃ (hle : A ≤ B) (H : is_conj_mem A B), is_simple $ B /ₘ (normal.𝒾 hle H)

@[simp] lemma chain_prop_def {A B : subgroup G} :
  chain_prop A B ↔ 
  ∃ (hle : A ≤ B) (H : is_conj_mem A B), is_simple $ B /ₘ (normal.𝒾 hle H) := iff.rfl

-- def chain_prop (A B : normal G) : Prop :=
--   ∃ (hle : A ≤ B), is_simple $ B /ₘ (normal.𝒾 hle)

-- @[simp] lemma chain_prop_def {A B : normal G} :
--   chain_prop A B ↔ 
--   ∃ (hle : A ≤ B), is_simple $ B /ₘ (normal.𝒾 hle) := iff.rfl

instance normal.inhabited : inhabited $ subgroup G := ⟨ ⊥ ⟩

/-- Chain is a nonempty list of subgroups such that subsequent subgroups 
  satisfies `chain_prop`, and furthermore, it begins with bot and ends with top -/
structure chain (G : Type) [group G] :=
(carrier    : list (subgroup G))
(nonempty   : carrier ≠ list.nil)
(chain_prop : carrier.chain' chain_prop)
(chain_head : carrier.head = ⊥)
(chain_last : carrier.last nonempty = ⊤)

lemma is_conj_mem_bot : is_conj_mem H ⊥ := λ _ _ _ hg, by simpa [mem_bot_iff.1 hg]

lemma is_conj_mem_bot' : is_conj_mem ⊥ H := λ _ ha _ _,
  by simp [mem_bot_iff.1 ha, one_mem]

def to_top : G →* (⊤ : subgroup G) := ⟨λ g, ⟨g, subgroup.mem_top _⟩, by tidy⟩
def to_top_iso : G ≅ (⊤ : subgroup G) := ⟨to_top, by tidy⟩

def top_div_bot_iso : 
  (⊤ : subgroup G) ≅ (⊤ : subgroup G) /ₘ (normal.𝒾 
    (@le_top _ _ (⊥ : subgroup G)) (is_conj_mem_bot' _)) := 
{ is_bijective := 
    begin
      refine ⟨_, by tidy⟩,
      rintros ⟨x₁, _⟩ ⟨x₂, _⟩ hx, dsimp at hx,
      rw [← coe_eq_mk, ← coe_eq_mk, mk_eq'] at hx,
      rw @normal.inclusion_inv _ _ (⊥ : subgroup G) _ bot_le at hx,
      erw @normal.inclusion_mul _ _ (⊥ : subgroup G) _ bot_le at hx,
      erw [normal.mem_𝒾, mem_bot_iff] at hx, 
      congr, rw ← group.inv_eq_of_mul_eq_one hx,
      exact group.inv_inv _,
    end .. 
    quotient.mk (normal.𝒾 (@le_top _ _ (⊥ : subgroup G)) (is_conj_mem_bot' _)) }

def top_div_bot_iso' : 
  G ≅ (⊤ : subgroup G) /ₘ (normal.𝒾 
    (@le_top _ _ (⊥ : subgroup G)) (is_conj_mem_bot' _)) := 
  group_hom.iso_comp to_top_iso top_div_bot_iso

def trivial_chain (h : is_simple G) : chain G := 
{ carrier := [⊥, ⊤],
  nonempty := by simp,
  chain_prop := 
    begin
      simp only [and_true, is_simple_def, list.chain'_singleton,
                 bot_le, chain_prop_def, exists_prop_of_true, ne.def, 
                 list.chain'_cons, group.nontrivial_def],
      exact ⟨is_conj_mem_bot' _, is_simple_of_iso top_div_bot_iso' h⟩, 
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

end composition

end mygroup
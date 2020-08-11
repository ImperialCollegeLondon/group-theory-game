import finiteness.finset2

universe u

open_locale classical

open set
def equiv.univ (X : Type u) :
X ≃ (univ : set X) :=
{ to_fun := λ x,  ⟨x, mem_univ x⟩,
  inv_fun := λ cx, cx.1,
  left_inv := by intro x; refl,
  right_inv := by intro cx; cases cx; refl }

/-! # Relation to fintype -/

def is_finite (X : Type u) : Prop := nonempty (fintype X)

attribute [class] is_finite

namespace is_finite

noncomputable def to_fintype (X : Type u) [is_finite X] : fintype X := classical.choice ‹_›

variable (X : Type u)

-- two concepts of finiteness are EQUIVALENT
theorem nonempty_fintype_iff_finite_univ : is_finite X ↔ finite (univ : set X) :=
begin
  split,
  { unfold finite,
    intro h,
    exact nonempty.map (fintype.equiv_congr (equiv.univ X)) h
  },
  { intro h,
    cases h,
    cases h with S hS,
    let elems : finset X := finset.map (equiv.to_embedding (equiv.univ X).symm) S,
    use { elems := elems, complete := begin
      intro x,
      change x ∈ finset.map (equiv.univ X).symm.to_embedding S,
      rw finset.mem_map,
      use ⟨x, mem_univ x⟩,
      split,
        apply hS,
      refl,
    end},
  }
end

instance set {X : Type u} [is_finite X] (s : set X) : is_finite ↥s :=
begin
  unfold is_finite at *,
  apply nonempty.map _ _inst_1,
  intro useless,
  resetI, -- puts all typeclasses in the local context into the inference system
  exact set_fintype s,
end

universe v

instance equiv_congr (X : Type u) {Y : Type v} [is_finite X] [nonempty (X ≃ Y)] :
  is_finite Y :=
begin
  tactic.unfreeze_local_instances,
  cases _inst_1,
  cases _inst_2 with e,
  use fintype.of_equiv X e,
end

instance infinite_prod {X : Type u} {Y : Type v} [infinite X] [nonempty Y] :
  infinite (X × Y) :=
begin
  tactic.unfreeze_local_instances,
  cases _inst_2 with y,
  apply infinite.of_injective (λ x, (x, y) : X → X × Y),
  rintros _ _ ⟨_, _⟩, refl,
end

--lemma not_finite_iff_infinite
lemma iff_not_infinite {X : Type u} : ¬ is_finite X ↔ infinite X :=
not_nonempty_fintype

lemma finite_or_infinite (X : Type u) : is_finite X ∨ infinite X :=
begin
  by_cases h : is_finite X,
    left, assumption,
  right, rwa ←iff_not_infinite,
end


/-! # card -/
-- not sure if this is more or less useful than fincard, but it seems
-- to be handy to have around
/-- ℕ-valued cardinality of an `is_finite` type -/
noncomputable def card (X : Type u) [is_finite X] : ℕ := 
@fintype.card X (to_fintype X)

lemma card_congr' {X : Type u} {Y : Type v} [is_finite X] [nonempty (X ≃ Y)] : 
card X = card Y :=
begin
  letI : fintype X := to_fintype X,
  letI : fintype Y := to_fintype Y,
  tactic.unfreeze_local_instances,
  cases _inst_2 with e,
  convert fintype.card_congr e,
end

lemma card_congr {X : Type u} {Y : Type v} [is_finite X] (e : X ≃ Y) :
by haveI : nonempty (X ≃ Y) := ⟨e⟩; exact
card X = card Y :=
begin
  letI : fintype X := to_fintype X,
  haveI : nonempty (X ≃ Y) := ⟨e⟩,
  letI : fintype Y := to_fintype Y,
  convert fintype.card_congr e,
end

lemma card_eq {X : Type u} {Y : Type v} [is_finite X] [is_finite Y] :
  card X = card Y ↔ nonempty (X ≃ Y) :=
begin
  split,
  { intro h,
    letI : fintype X := to_fintype X,
    letI : fintype Y := to_fintype Y,
    rwa ←fintype.card_eq,
  },
  { rintro ⟨e⟩,
    exact card_congr e,
  }
end

instance {X : Type u} {Y : Type v} [is_finite X] [is_finite Y] :
  is_finite (X × Y) :=
begin
  letI : fintype X := to_fintype X,
  letI : fintype Y := to_fintype Y,
  split,
  apply_instance
end

local attribute [instance] to_fintype

lemma card_prod (X : Type u) (Y : Type v) [is_finite X] [is_finite Y] :
card (X × Y) = card X * card Y := 
by { unfold card, convert fintype.card_prod X Y }

end is_finite


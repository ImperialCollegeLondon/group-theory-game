/-
Finite types
-/
import tactic set_theory.cardinal

/-
universe u

def finite (X : Type u) := nonempty (fintype X)

attribute [class] finite

-- let's make an API for finite types

#check fintype.of_subsingleton

instance : finite pempty := ⟨by apply_instance⟩
instance : finite empty := ⟨by apply_instance⟩
instance : finite punit := ⟨by apply_instance⟩
instance : finite bool := ⟨by apply_instance⟩

open_locale classical
noncomputable theory

instance finite.of_subsingleton (X : Sort*) [subsingleton X] : finite X :=
@classical.by_cases (nonempty X) (finite X) (λ ⟨x⟩, ⟨fintype.of_subsingleton x⟩) $ λ h, ⟨⟨∅, λ x, h ⟨x⟩⟩⟩
open function

lemma finite.of_inj (X : Sort*) [h : finite X] (Y : Sort*) (f : Y → X) (hf : injective f) : finite Y :=
let ⟨h⟩ := h in ⟨@fintype.of_injective Y X h f hf⟩

lemma finite.of_surj (X : Sort*) [h : finite X] (Y : Sort*) (f : X → Y) (hf : surjective f) : finite Y :=
let ⟨h⟩ := h in ⟨@fintype.of_surjective X Y h _ f hf⟩

lemma finite_iff_card_nat (X : Sort*) : finite X ↔ ∃ n : ℕ, cardinal.mk X = n :=
cardinal.lt_omega_iff_fintype.symm.trans cardinal.lt_omega

-/


open_locale classical
noncomputable theory

def fincard (X : Type*) : ℕ :=
if h : nonempty (fintype X) then @fintype.card X (classical.choice h) else 0 

@[simp] theorem card_eq_fincard (X : Type*) [h : fintype X] : fintype.card X = fincard X :=
begin
  simp [fincard, nonempty.intro h],
  congr,
end

theorem fincard_eq_zero {X : Type*} (h : ¬nonempty (fintype X)) : fincard X = 0 := dif_neg h

@[simp] lemma fincard.empty : fincard empty = 0 :=
begin
  simp [←card_eq_fincard]
end

lemma fincard.of_equiv {X Y : Type*} (h : X ≃ Y) : fincard X = fincard Y :=
begin
  by_cases h2 : nonempty (fintype X),
  { cases h2,
    resetI,
    letI : fintype Y := fintype.of_equiv X h,
    rw [←card_eq_fincard X, ←card_eq_fincard Y, fintype.of_equiv_card],
  },
  { have h3 : ¬nonempty (fintype Y),
    { rintros ⟨_⟩,
      exactI h2 ⟨fintype.of_equiv _ h.symm⟩ },
    simp [fincard_eq_zero, *] }
end

theorem fincard.of_empty {X : Type*} (hX : X → false) : fincard X = 0 :=
by simp [fincard.of_equiv (equiv.equiv_empty hX)]

private theorem fincard.prod_of_empty_left {X : Type*} (h : X → false) (Y : Type*) :
  fincard (X × Y) = fincard X * fincard Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.fst), zero_mul]

private theorem fincard.prod_of_empty_right (X : Type*) {Y : Type*} (h : Y → false) :
  fincard (X × Y) = fincard X * fincard Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.snd), mul_zero]

private theorem fincard.prod_of_finite {X Y : Type*}
  (hX : nonempty (fintype X)) (hY : nonempty (fintype Y)) :
fincard (X × Y) = fincard X * fincard Y :=
begin
  unfreezingI {cases hX with hX, cases hY with hY},
  -- change this to squeeze_simp and watch Lean time out
  simp [←card_eq_fincard],
end

private theorem fincard.prod_of_infinite_left {X Y : Type*}
  (hX : ¬nonempty (fintype X)) (hY : nonempty Y) :
fincard (X × Y) = fincard X * fincard Y :=
begin
  have h : ¬nonempty (fintype (X × Y)),
  { rw not_nonempty_fintype at ⊢ hX,
    unfreezingI {cases hY with y},
    apply infinite.of_injective (λ x, (x, y) : X → X × Y),
    rintros _ _ ⟨_, _⟩, refl
  },
  simp [fincard_eq_zero, *],
end

private theorem fincard.prod_of_infinite_right {X Y : Type*}
  (hX : nonempty X) (hY : ¬nonempty (fintype Y)) : 
fincard (X × Y) = fincard X * fincard Y :=
begin
  have h : ¬nonempty (fintype (X × Y)),
  { rw not_nonempty_fintype at ⊢ hY,
    unfreezingI {cases hX with x},
    apply infinite.of_injective (prod.mk x : Y → X × Y),
    rintros _ _ ⟨_, _⟩, refl
  },
  simp [fincard_eq_zero, *],
end

theorem fincard.prod (X Y : Sort*) : fincard (X × Y) = fincard X * fincard Y :=
begin
  by_cases hX : X → false,
  { exact fincard.prod_of_empty_left hX _},
  rw [←not_nonempty_iff_imp_false, not_not] at hX,
  by_cases hY : Y → false,
  { exact fincard.prod_of_empty_right _ hY},
  rw [←not_nonempty_iff_imp_false, not_not] at hY,
  by_cases hX2 : nonempty (fintype X),
  { by_cases hY2 : nonempty (fintype Y),
    { exact fincard.prod_of_finite hX2 hY2},
    { exact fincard.prod_of_infinite_right hX hY2},
  },
  { exact fincard.prod_of_infinite_left hX2 hY}
end

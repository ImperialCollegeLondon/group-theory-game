--old
#exit

/-
fincard -- ℕ-valued cardinality of a type (zero for infinite types)
-/
import tactic finiteness.is_finite

open_locale classical
noncomputable theory

def fincard (X : Type*) : ℕ :=
if h : is_finite X then @fintype.card X (classical.choice h) else 0 

@[simp] theorem fintype.card_eq_fincard (X : Type*) [h : fintype X] : fintype.card X = fincard X :=
begin
  simp [fincard, nonempty.intro h, is_finite],
  congr,
end

open is_finite

@[simp] theorem is_finite.card_eq_fincard' (X : Type*) [h : is_finite X] :
  @fintype.card X (is_finite.to_fintype X) = fincard X :=
begin
  haveI : fintype X := to_fintype X,
  convert fintype.card_eq_fincard X,
end

@[simp] theorem is_finite.card_eq_fincard (X : Type*) [h : is_finite X] :
  is_finite.card X = fincard X := is_finite.card_eq_fincard' X

example (X : Type) (a b : is_finite X) : a = b := rfl

theorem fincard_eq_zero {X : Type*} [h : infinite X] : fincard X = 0 := dif_neg (not_nonempty_fintype.2 h)

@[simp] lemma fincard.empty : fincard empty = 0 :=
begin
  simp [←fintype.card_eq_fincard]
end

lemma fincard.of_equiv {X Y : Type*} (h : X ≃ Y) : fincard X = fincard Y :=
begin
  casesI finite_or_infinite X,
  { haveI : nonempty (X ≃ Y) := ⟨h⟩,
    rw [←is_finite.card_eq_fincard X, ←is_finite.card_eq_fincard Y], convert is_finite.card_congr h,
  },
  { haveI : infinite Y := infinite.of_injective _ (equiv.injective h),
    simp [fincard_eq_zero] },
end

theorem fincard.of_empty {X : Type*} (hX : X → false) : fincard X = 0 :=
by simp [fincard.of_equiv (equiv.equiv_empty hX)]

private theorem fincard.prod_of_empty_left {X : Type*} (h : X → false) (Y : Type*) :
  fincard (X × Y) = fincard X * fincard Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.fst), zero_mul]

private theorem fincard.prod_of_empty_right (X : Type*) {Y : Type*} (h : Y → false) :
  fincard (X × Y) = fincard X * fincard Y :=
by rw [fincard.of_empty h, fincard.of_empty (h ∘ prod.snd), mul_zero]

/-! Products -/
private theorem fincard.prod_of_finite {X Y : Type*}
  (hX : is_finite X) (hY : is_finite Y) :
fincard (X × Y) = fincard X * fincard Y :=
begin
  convert is_finite.card_prod X Y;
  simp,
end

private theorem fincard.prod_of_infinite_left {X Y : Type*}
  [infinite X] [nonempty Y] :
fincard (X × Y) = fincard X * fincard Y :=
begin
  simp [fincard_eq_zero, *]
end

private theorem fincard.prod_of_infinite_right {X Y : Type*}
  (hX : nonempty X) (hY : infinite Y) : 
fincard (X × Y) = fincard X * fincard Y :=
begin
  rw mul_comm,
  rw ←fincard.prod_of_infinite_left,
  apply fincard.of_equiv,
  exact equiv.prod_comm X Y,
end

theorem fincard.prod (X Y : Sort*) : fincard (X × Y) = fincard X * fincard Y :=
begin
  by_cases hX : X → false,
  { exact fincard.prod_of_empty_left hX _},
  rw [←not_nonempty_iff_imp_false, not_not] at hX,
  by_cases hY : Y → false,
  { exact fincard.prod_of_empty_right _ hY},
  rw [←not_nonempty_iff_imp_false, not_not] at hY,
  casesI finite_or_infinite X with hX2 hX2,
  { casesI finite_or_infinite Y with hY2 hY2,
    { exact fincard.prod_of_finite hX2 hY2},
    { exact fincard.prod_of_infinite_right hX hY2},
  },
  { exact fincard.prod_of_infinite_left}
end

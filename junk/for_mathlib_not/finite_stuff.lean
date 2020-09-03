-- old
#exit

import data.set.finite
import tactic
import finiteness.is_finite

-- def is_fintype 

/- Avigad's notes on dealing with finite sums and cardinality -/

noncomputable theory

open_locale classical

namespace set

variables {α : Type*} {β : Type*}

attribute [class] finite infinite

section

variable [add_comm_monoid β]

def sum (s : set α) (f : α → β) : β :=
if h : finite s then h.to_finset.sum f else 0

def sum_zero_of_not_finite {s : set α} (h : ¬ finite s) (f : α → β) : sum s f = 0 :=
dif_neg h

def sum_zero_of_infinite {s : set α} [infinite s] (f : α → β) : sum s f = 0 :=
dif_neg (show infinite s, by apply_instance)

def sum_def_of_finite {s : set α} [h : finite s] (f : α → β) : sum s f = h.to_finset.sum f :=
dif_pos h

lemma sum_ext {s t : set α} {f₁ f₂ : α → β} (h₀ : s = t) (h₁ : ∀ x ∈ t, f₁ x = f₂ x) :
  sum s f₁ = sum t f₂ :=
if h' : finite s then
  begin
    haveI h'' : finite t := by rw [←h₀]; assumption,
    rw [sum, sum, dif_pos h', dif_pos h''],
    apply finset.sum_congr,
    { ext, simp only [finite.mem_to_finset, h₀] },
    intro x, rw [finite.mem_to_finset], apply h₁
  end
else
  begin
    haveI h'' : ¬ finite t := by rw [←h₀]; assumption,
    rw [sum, sum, dif_neg h', dif_neg h'']
  end
end

def card (s : set α) : ℕ :=
s.sum (λ x, 1)

lemma card_zero_of_not_finite {s : set α} (h : ¬ finite s) : card s = 0 :=
dif_neg h

lemma card_def_of_finite' {s : set α} [h : finite s] : card s = h.to_finset.sum (λ x, 1) :=
dif_pos h

lemma card_def_of_finite {s : set α} [h : finite s] : card s = finset.card (h.to_finset) :=
by rw [card_def_of_finite', finset.card_eq_sum_ones]

lemma finite_or_infinite (s : set α) : finite s ∨ infinite s := classical.em _

instance set.finite.fintype' {α : Type*} {s : set α} [s.finite] : fintype s :=
set.finite.fintype $ by apply_instance

instance finite_inter {α : Type*} {s t : set α} [s.finite] : (s ∩ t).finite :=
finite.subset (by apply_instance : finite s) $ inter_subset_left _ _

lemma to_finset_inter' {α : Type*} (s t : set α) [s.finite] [t.finite] :
  (s ∩ t).to_finset = s.to_finset ∩ t.to_finset :=
by ext; simp

/-- Two sets are disjoint iff they are disjoint as finsets. -/
lemma disjoint_finset_iff_disjoint {α : Type*} {s t : set α} [finite s] [finite t]:
  disjoint s t ↔ disjoint s.to_finset t.to_finset :=
begin
  rw [disjoint, disjoint, le_bot_iff, le_bot_iff],
  change _ ∩ _ = ∅ ↔ _ ∩ _ = ∅,
  rw ←set.to_finset_inter',
  split,
  { intro h, simp_rw h, ext, simp },
  { intro h, ext, rw ←set.mem_to_finset, rw h, simp }
end

lemma Union_to_finset_eq_bind {ι α : Type*} [fintype ι] [fintype α] (f : ι → set α) :
  (⋃ i : ι, f i).to_finset = (finset.univ : finset ι).bind(λ i, (f i).to_finset) := by ext; simp

universe v

lemma foo (s : set α) [finite s] (β : Type v) [add_comm_monoid β] (f : α → β) :
  s.to_finset.sum f = finset.univ.sum (λ (a : s), f a.1) :=
begin
  symmetry,
  convert finset.sum_subtype_of_mem _ _,
  { ext x,
    cases x with x hx,
    simp [hx]
  },
  by apply_instance,
  simp
end


lemma card_sUnion (s : set (set α)) [finite s] (h1 : ∀ a ∈ s, finite a)
    (h2 : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ∩ b = ∅) :
  card s.sUnion = s.sum (λ a, card a) :=
begin
  haveI : finite s.sUnion := finite.sUnion (by apply_instance) h1,
  simp_rw ←subset_empty_iff at h2,
  change ∀ a ∈ s, ∀ b ∈ s, a ≠ b → disjoint a b at h2,
  let t : s → finset α := λ x, (@set.to_finset _ x.1 (set.finite.fintype (h1 x.1 x.2))),
  have h : ∀ (x : s), x ∈ (finset.univ : finset s) → ∀ (y : s), y ∈ (finset.univ : finset s) → x ≠ y → disjoint (t x) (t y),
  { rintros ⟨a, ha⟩ h4 ⟨b, hb⟩ h3 h,
    have h' : a ≠ b, rintro rfl, apply h, refl,
    rw ←disjoint_finset_iff_disjoint,
    convert h2 a ha b hb h' },
  convert @finset.card_bind s α _ (finset.univ : finset s) t h,
  { rw card_def_of_finite,
    apply congr_arg,
    ext x,
    rw finset.mem_bind,
    show x ∈ to_finset _ ↔ _,
    rw mem_to_finset,
    rw mem_sUnion,
    finish },
  rw sum_def_of_finite,
  change s.to_finset.sum _ = _,
  rw foo s _ (λ a : set α, a.card),
  congr',
  ext x,
  cases x with S hS,
  dsimp [t],
  haveI := h1 S hS,
  exact @card_def_of_finite _ S _,
end

lemma sum_linear [comm_semiring β] (s : set α) (c : β) (f : α → β) :
  s.sum (λx, c * f x) = c * s.sum f :=
begin
  casesI finite_or_infinite s,
  { rw [sum_def_of_finite, sum_def_of_finite],
    exact (finite.to_finset h).sum_hom (has_mul.mul c) },
  { simp [sum_zero_of_not_finite h, card_zero_of_not_finite h] }
end

lemma sum_const (s : set α) (c : ℕ):
  s.sum (λx, c) = c * card s :=
begin
  unfold card,
  rw ←sum_linear s c (λ a, 1),
  simp
end

lemma card_image_of_inj_on' {s : set α} [finite s] {f : α → β}
  (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) :
    card (f '' s) = card s :=
begin
  haveI : finite (f '' s) := by {
    rw finite_image_iff, assumption,
    exact h },
  rw card_def_of_finite,
  rw card_def_of_finite,
  have h' : ∀ (x : α), x ∈ _inst_1.to_finset → ∀ (y : α), y ∈ _inst_1.to_finset → f x = f y → x = y,
    intros x hx y hy,
    change x ∈ to_finset _ at hx,
    change y ∈ to_finset _ at hy,
    rw mem_to_finset at hx hy,
  exact h x hx y hy,
  convert finset.card_image_of_inj_on h',
  ext x,simp
end


end set
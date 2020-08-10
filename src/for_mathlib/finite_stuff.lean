import data.set.finite
import tactic

#check infinite
#check set.finite

-- def is_fintype 

/- This section added by JDA, to deal with finite sums and cardinality -/

noncomputable theory
open_locale classical

namespace set

variables {α : Type*} {β : Type*}

attribute [class] finite

section

variable [add_comm_monoid β]

def sum (s : set α) (f : α → β) : β :=
if h : finite s then h.to_finset.sum f else 0

def sum_zero_of_not_finite {s : set α} (h : ¬ finite s) (f : α → β) : sum s f = 0 :=
dif_neg h

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

def card_zero_of_not_finite {s : set α} (h : ¬ finite s) : card s = 0 :=
dif_neg h

def card_def_of_finite {s : set α} [h : finite s] : card s = h.to_finset.sum (λ x, 1) :=
dif_pos h

lemma card_sUnion (s : set (set α)) [finite s] (h: ∀ a ∈ s, finite a)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a ∩ b = ∅) :
  card s.sUnion = s.sum (λ a, card a) :=
begin
  sorry
end

lemma sum_const [comm_semiring β] (s : set α) (c : β):
  s.sum (λx, c) = c * card s :=
begin
  by_cases h : finite s,
  { haveI := h,
    rw [sum_def_of_finite, card_def_of_finite],

    sorry},
  { simp [sum_zero_of_not_finite h, card_zero_of_not_finite h] }
end

lemma card_image_of_inj_on' {s : set α} [finite s] {f : α → β}
  (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → f x = f y → x = y) :
    card (f '' s) = card s :=
sorry

end set
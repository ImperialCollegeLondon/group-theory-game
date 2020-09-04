import orbit.basic

namespace mygroup

open classical function set mygroup.subgroup mygroup.group
variables {G : Type} [group G]

-- The normalizer of a subset of G is a subgroup of G 
def normalizer_of_set (A : set G) : subgroup G := 
{ carrier := { g : G | ∀ n, n ∈ A ↔ g * n * g⁻¹ ∈ A },
  one_mem' := by intro a; rw [group.one_mul, group.one_inv, group.mul_one],
  mul_mem' := λ _ _ hx hy _, by rw [hy, hx]; simp [group.mul_assoc],
  inv_mem' := λ x hx a, by rw hx (x⁻¹ * a * x⁻¹⁻¹); simp [group.mul_assoc] }

lemma mem_normalizer_of_set_iff [group G] {H : subgroup G} (x : G):
  x ∈ normalizer_of_set H.carrier ↔ ∀ k : G, k ∈ H ↔ x * k * x⁻¹ ∈ H := by refl

def normalizer (H : subgroup G) := stabilizer (conjugation_action) H

lemma mem_normalizer_def  {H : subgroup G} (x : G) :
  x ∈ normalizer H ↔ {k : G | ∃ (h : G) (H : h ∈ H), k = x * h * x⁻¹} = H := 
subgroup.ext'_iff.symm

lemma mem_normalizer_iff {H : subgroup G} (x : G):
  x ∈ normalizer H ↔ ∀ k : G, k ∈ H ↔ x * k * x⁻¹ ∈ H := 
begin
  rw mem_normalizer_def, split,
  { intros hx s,
    rw ext_iff at hx, specialize hx (x * s *x⁻¹) ,
    dsimp at hx, rw mem_coe' at hx, rw ← hx,
    split,
    { rintro hs, use [s, hs] },
    { rintro ⟨h, hh, hsx⟩, convert hh,
      exact group.mul_left_cancel x _ _ (mul_right_cancel x⁻¹ _ _ hsx) } },
  { intro hx, ext y, split,
    { rintro ⟨s, hs, rfl⟩, exact ( hx s ).1 hs},
    { intro hy, refine ⟨x⁻¹ * y * x, _, _⟩,
        { change y ∈ H at hy,
          convert (hx (x⁻¹ * y * x)).2 _,
          convert hy,
          simp [group.mul_assoc] },
        { simp [group.mul_assoc] } } }
end  

lemma normalizer_eq_normalizer_of_set (H : subgroup G) : 
  (normalizer H  : set G) = { g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H } := 
by { ext, rw [subgroup.mem_coe', mem_normalizer_iff], refl }

lemma normalizer_of_set_eq_normalizer (H : subgroup G) : 
  normalizer_of_set H.carrier = normalizer H :=
begin
  apply subgroup.ext'_iff.1,
  change (normalizer_of_set H.carrier).carrier = normalizer H,
  rw normalizer_eq_normalizer_of_set, refl,
end

lemma le_normalizer (H : subgroup G) : H ≤ normalizer H :=
begin
  intros g hg,
  apply (mem_normalizer_iff _).2,
  intro k,
  split,
    intro hk, 
    apply H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg),
  intro hk,
  suffices : g⁻¹ * (g * k * g⁻¹) * g ∈ H,
    convert this; simp [group.mul_assoc], 
  apply H.mul_mem (H.mul_mem (H.inv_mem hg) hk) hg
end

end mygroup
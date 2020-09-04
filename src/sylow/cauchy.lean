import sylow.cyclic_vector_action
import sylow.card_of_list

/-!
# Cauchy's Theorem.

https://en.wikipedia.org/wiki/Cauchy%27s_theorem_(group_theory)

If a finite group $G$ has order a multiple of $p$ then
$G$ has an element of order $p$.

# Main Definitions.

## variables

(G : Type)
[group G]
(n : ℕ)

-/

namespace mygroup


open_locale classical
open mygroup.subgroup list mygroup.group

universes u v w
variables {G : Type} [group G]

--local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

/- want to prove the theorem that says
   that if p | |G| then G has an element of order p

   Proposed proof:

1) Let X be the set of lists of p elements of G whose product is 1 
  -- a definition and hence a stroke of genius.
  -- Status : DONE
2) Note that cyclic shift is a permutation of X
3) Note that #X=|G|^{p-1} is a multiple of p
4) Hence # fixed point is a multiple of p by some standard theorem
5) and # fixed points is at least 1 (the identity)
6) so it's at least 2 and there's an element of order p

-/

-- #check array -- for computing

--lemma group.mul_left_inj : ∀ (a b c : G), b * a = c * a ↔ b = c :=
--mul_right_cancel_iff

--lemma group.inv_mul_self (a : G) : a⁻¹ * a = 1 := group.mul_left_inv a

--instance : is_associative G (*) := ⟨group.mul_assoc⟩

open list

theorem cauchy_elements (G : Type) [group G] [fintype G] (p : ℕ) (hp : p.prime)
  (hpG : p ∣ fincard' G) : p ∣ fincard' {g : G // ⦃p⦄^g = 1} :=
begin
  cases p with n, rcases hp with ⟨⟨⟩, _⟩,
  have h := card_set_congr_card_fixed_points_mod_prime (cool_action G n) n.succ hp 1,
  have h2 : fincard' (cyclic ↑(n.succ)) = n.succ ^ 1,
    rw [nat.pow_one, cyclic.fincard_cyclic], simp,
  specialize h h2, rw card_cool_set at h,
  cases n with m, cases hp, cases hp_left, cases hp_left_a,
  have h1 : m.succ.succ ∣ fincard' G ^ m.succ,
    rw nat.pow_succ,
    apply dvd_mul_of_dvd_right hpG,
  rw ←nat.modeq.modeq_zero_iff at h1 ⊢,
  have h2 := nat.modeq.trans (nat.modeq.symm h) h1,
  convert h2 using 1,
  have h3 := fixed_points_eq_roots G m.succ,
  exact fincard.of_equiv h3.symm
end

theorem cauchy_elememt (G : Type) [group G] [fintype G] (p : ℕ) (hp : p.prime)
  (hpG : p ∣ fincard' G) : ∃ g : G, g ≠ 1 ∧ ⦃p⦄^g = 1 :=
begin
  by_contra h, push_neg at h,
  have h1 : ∀ g : G, ⦃p⦄^g = 1 ↔ g = 1,
    intro g, split,
      { rintro h3, by_contra h2, exact h g h2 h3 },
      { rintro rfl, simp },
  have h2 := cauchy_elements G p hp hpG,
  let e : {g : G // ⦃p⦄^g = 1} ≃ {g : G // g = 1} :=
    { to_fun := λ g, ⟨g.1, (h1 g).1 g.2⟩,
      inv_fun := λ g, ⟨g.1, (h1 g).2 g.2⟩,
      left_inv := by {intro g, cases g, simp},
      right_inv := by {intro g, cases g, simp} },
  rw fincard.of_equiv e at h2,
  change p ∣ fincard' ({(1 : G)} : set G) at h2,
  rw [fincard.card_singleton_eq_one, nat.dvd_one] at h2,
  subst h2, cases hp, cases hp_left, cases hp_left_a,
end

-- theorem prime_lemma (G : Type) [group G] (p : ℕ) (hp : p.prime) (g : G)
--   (hg1 : g ≠ 1) (hg2 : ⦃p⦄^g = 1) : 
--   (group_hom.kernel (to_hom_cyclic g p hg2)).to_subgroup = ⊥ :=
-- begin
--   sorry
-- end

theorem order_map_image_eq (g : G) : (order_map g).image = closure {g} :=
begin
  rw cyclic.closure_singleton_eq,
  ext, split; rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩,
end

-- theorem prime_lemma4 (G : Type) [group G] (p : ℕ) (hp : p.prime) (g : G)
--   (hg1 : g ≠ 1) (hg2 : ⦃p⦄^g = 1) : (order_map g).image = closure {g} := sorry

theorem gcd_lemma (g : G) (a b : ℕ) (ha : ⦃a⦄^g = 1) (hb : ⦃b⦄^g = 1) :
  ⦃(nat.gcd a b)⦄^g = 1 :=
begin
  rw nat.gcd_eq_gcd_ab a b,
  rw [group.pow_add, _root_.mul_comm, group.pow_mul],
  rw ha, rw group.pow_one,
  rw [_root_.mul_comm, group.pow_mul],
  rw hb, rw group.pow_one,
  rw group.mul_one,
end

lemma group.inv_one : (1 : G)⁻¹ = 1 :=
begin
  symmetry,
  apply group.eq_inv_of_mul_eq_one,
  rw group.mul_one,
end

lemma easy (g : G) (a : ℤ) : ⦃a⦄^g = 1 ↔ ⦃int.nat_abs a⦄^g = 1 :=
begin
  cases int.nat_abs_eq a,
  { congr' },
  { conv_lhs begin 
      rw h,
      rw group.pow_neg,
    end,
    split,
      rintro h2, 
      rw ←pow_inv at h2,
      rw group.inv_eq at h2,
      rw ←h2,
      rw group.inv_one,
    intro h2,
    rw ←pow_inv,
    rw group.inv_eq,
    rw h2,
    rw group.inv_one,
   }

end

theorem int_gcd_lemma (g : G) (a b : ℤ) (ha : ⦃a⦄^g = 1) (hb : ⦃b⦄^g = 1) :
  ⦃(int.gcd a b)⦄^g = 1 :=
begin
  apply gcd_lemma; rw ←easy; assumption
end

theorem aux_lemma1 {p : ℕ} (hp : p.prime) {g : G} (hg : g ≠ 1) 
  (hpg : ⦃p⦄^g = 1) {k : ℤ} (hkg : ⦃k⦄^g = 1) : (p : ℤ) ∣ k :=
begin
  by_contra hk,
  set t := int.gcd p k with ht,
  have ht2 : t = 1,
    have := nat.gcd_dvd (int.nat_abs p) (int.nat_abs k),
    unfold int.gcd at ht,
    rw ←ht at this,
    cases this with h3 h4,
    change t ∣ p at h3,
    rw nat.dvd_prime hp at h3,
    cases h3, exact h3,
    exfalso,
    apply hk,
    rw h3 at h4,
    exact int.coe_nat_dvd_left.mpr h4,
  apply hg,
  convert int_gcd_lemma g p k hpg hkg,
  rw ←ht,
  rw ht2,
  rw int.coe_nat_one,
  rw group.one_pow,
end

theorem aux_lemma2 (p : ℕ) (hp : p.prime) (g : G)
  (hg1 : g ≠ 1) (hg2 : ⦃p⦄^g = 1) : (order_map g).kernel = mod ↑p :=
begin
  ext x, rw group_hom.mem_kernel, split; intro hx,
    { exact aux_lemma1 hp hg1 hg2 hx },
    { rcases hx with ⟨k, rfl⟩,
      change ⦃p * k⦄^g = _,
      rw [int.mul_comm, group.pow_mul, hg2, group.pow_one] }
end

def eq_equiv (G : Type) [group G] (H K : subgroup G) (i : H = K) : H ≃ K :=
{ to_fun := λ h, ⟨h.1, i ▸ h.2⟩,
  inv_fun := λ k, ⟨k.1, i.symm ▸ k.2⟩,
  left_inv := λ h, by ext; refl,
  right_inv := λ k, by ext; refl }

theorem key_lemma (G : Type) [group G] (p : ℕ) (hp : p.prime) (g : G)
  (hg1 : g ≠ 1) (hg2 : ⦃p⦄^g = 1) : 
  fincard' (closure ({g} : set G)) = p := 
begin
  have h := quotient.quotient_kernel_iso_image (order_map g),
  rw fincard.of_equiv (eq_equiv G _ _ (order_map_image_eq g).symm),
  have h2 := group_hom.mul_equiv_of_iso h,
  replace h2 := mul_equiv.to_equiv h2,
  rw fincard.of_equiv h2.symm,
  convert cyclic.fincard_cyclic p (nat.prime.pos hp),
  apply aux_lemma2 p hp g hg1 hg2,
end

theorem cauchy (G : Type) [group G] [fintype G] (p : ℕ) (hp : p.prime)
  (hpG : p ∣ fincard' G) : ∃ H : subgroup G, fincard' H = p := 
begin
  rcases cauchy_elememt G p hp hpG with ⟨g, hg1, hg2⟩,
  use closure {g},
  apply key_lemma G p hp g hg1 hg2
end

end mygroup

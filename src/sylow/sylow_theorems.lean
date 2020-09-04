import sylow.cauchy orbit.normalizer

namespace mygroup

variables {G : Type} [group G]
open classical function set mygroup.subgroup mygroup.group mygroup.group_hom

-- Definition of p-group for finite groups, not using definition of order of 
-- an element explicitly
class p_group [fintype G] (p : ℕ) extends group G :=
(card_pow_p: ∃ n : ℕ , fincard' G = p^n)

-- A p-subgroup is a subgroup of a group G which is itself a p-group
class p_subgroup (G : Type) [group G] [fintype G] (p : ℕ) extends subgroup G :=
(card_pow_p: ∃ n : ℕ , fincard' (carrier) = p^n)

def is_p_subgroup (H : subgroup G) (p : ℕ) : Prop := 
  ∃ n : ℕ , fincard' (H) = p ^ n 

def is_lcoset (H : subgroup G) (B : set G) : Prop := ∃ g : G, B = lcoset g H

def lcosets (H : subgroup G) := {B : set G // is_lcoset H B}

def dumb_fun' (H : subgroup G) (g : G) (X : set G) : set G :=
  {t | ∃ x ∈ X , t = g * x}

lemma dumb_fun_lcoset_eq (g h : G) (H : subgroup G) : 
  dumb_fun' H h (g ⋆ H) = h * g ⋆ H :=
begin
  ext, split, 
  { rintro ⟨x, ⟨h', hh', rfl⟩, rfl⟩,
    exact ⟨h', hh', (group.mul_assoc _ _ _).symm⟩ },
  { rintro ⟨h', hh', rfl⟩,
    refine ⟨g * h', ⟨h', hh', rfl⟩, group.mul_assoc _ _ _⟩ }
end

def dumb_fun (H : subgroup G) (g : G) (X : lcosets H) : lcosets H :=
⟨dumb_fun' H g X.1, 
  begin
  rcases X with ⟨g', ⟨w, rfl⟩⟩, 
  use g * w, ext, split,
    { intro hx,
      rcases hx with ⟨hx_w, ⟨h, hh, rfl⟩, rfl⟩,
      use h,
      simpa [group.mul_assoc] },
    { rintro ⟨h, hh, rfl⟩,
      use w * h,
      simpa [group.mul_assoc] }
  end⟩

def laction.comap {H : Type} [group H] (f : H →* G) (S : Type) (μ : laction G S) :
  laction H S := 
{ to_fun := λ h s, f h •[μ] s,
  map_one' := λ s, (map_one f).symm ▸ μ.map_one s,
  map_assoc' := λ g h s, (map_mul f g h).symm ▸ μ.map_assoc' _ _ _ }

def dumb_action (H : subgroup  G) : laction G (lcosets H) := 
{ to_fun := dumb_fun H,
  map_one' := 
  begin 
    intro S, unfold dumb_fun, dsimp, unfold dumb_fun', simp
  end,  
  map_assoc' := 
  begin
    rintros g h ⟨_, g', rfl⟩,
    unfold dumb_fun, unfold dumb_fun',
    norm_num, ext1, norm_num, split,
      { rintro ⟨_, ⟨t, ⟨s, ⟨hs, ht⟩⟩, rfl⟩, rfl⟩,
        use t, split, use [s, hs], exact ht,
        rw group.mul_assoc },
      { rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩,
        iterate 3 { split }, use [s, hs], 
        simp [group.mul_assoc] }    
  end }

def dumb_action' (H : subgroup G) : laction H (lcosets H) :=
laction.comap (𝒾 H) (lcosets H) (dumb_action H)

def normal_in_normalizer_of_set (H : subgroup G) : normal (normalizer_of_set H.carrier) := 
{ conj_mem' := 
    begin 
      intros n hnorm g,
      dsimp at *,   
      cases g with g hg,
      cases n with n hn,
      rw mem_coe,
      rw mem_comap',
      norm_num,
      change g ∈ normalizer_of_set H.carrier at hg,
      rw mem_normalizer_of_set_iff at hg,
      specialize hg n,
      rw ← hg,
      unfold comap at hnorm,
      rw mem_preimage at hnorm,
      change n ∈ H at hnorm,
      assumption,
    end,
  .. comap (𝒾 (normalizer_of_set H.carrier)) H }

def to_lcosets (g : G) (H : subgroup G) : lcosets H := ⟨g ⋆ H, ⟨g, rfl⟩⟩

lemma aux_lemma [fintype G] (H : subgroup G) (g : G) :
  (H : set G) ≤ conjugate_subgroup g H ↔ g ∈ normalizer H :=
⟨begin
  intro h,
  show conjugate_subgroup g H = H,
  apply subgroup.ext',
  symmetry,
  apply fincard.eq_of_card_eq_subset,
    exact h,
  change fincard' H = fincard' (conjugate_subgroup g H),
  apply fincard.of_equiv,
  apply mul_equiv.to_equiv,
  apply mul_equiv_of_is_conjugate,
  exact conjugate_is_conjugate g H
end, begin
  intro h,
  change conjugate_subgroup g H = H at h,
  conv_lhs {rw ←h},
  apply subset.refl
end⟩

lemma foo [fintype G] (H : subgroup G) (g : G):
to_lcosets g H  ∈ (fixed_points (dumb_action' H)) ↔ g ∈ normalizer H :=
begin
  rw ←aux_lemma,
  unfold fixed_points, 
  unfold to_lcosets,
  unfold dumb_action', 
  unfold dumb_action,
  unfold laction.comap,
  simp,
  unfold dumb_fun,
  simp,
  unfold dumb_fun',
  unfold conjugate_subgroup,
  simp,
  unfold_coes,
  simp,
  split,
  { intros h1 h hh,
    specialize h1 ⟨h, hh⟩,
    simp * at *,
    use g⁻¹ * h * g,
    rw ext_iff at h1,
    specialize h1 (h * g),
    have h2 : h * g ∈ g ⋆ H,
      rw ←h1,
      use g,
      use 1,
      use H.one_mem,
      rw group.mul_one,
      rcases h2 with ⟨j, hj1, hj2⟩,
      rw group.mul_assoc,
      rw hj2,
      rw [← group.mul_assoc, group.mul_left_inv, group.one_mul],
      use hj1,
      rw ← hj2,
      simp [group.mul_assoc] },
  { rintros h1 ⟨h, hh⟩,
    ext x, split,
    { rintro ⟨_, ⟨k, hk1, rfl⟩, rfl⟩,
      rcases h1 hh with ⟨w, hw, rfl⟩,
      show g * w * g⁻¹ * _ ∈ _,
      use w * k,
      use H.mul_mem hw hk1,
      simp [group.mul_assoc]
    },
    { rintro ⟨j, hx, rfl⟩,
      rw set.mem_set_of_eq,
      rcases h1 hh with ⟨w, hw, rfl⟩,
      use g*w⁻¹*j,
      split,
        use w⁻¹*j,
        split,
          apply H.mul_mem (H.inv_mem hw) hx,
        rw group.mul_assoc,
      simp [group.mul_assoc] } }
end

def projection [fintype G] (H : subgroup G) :
  normalizer H → fixed_points (dumb_action' H) :=
λ h, ⟨to_lcosets h.1 H, (foo H h.1).2 h.2⟩

lemma proj_eq_coset [fintype G] (H : subgroup G) (b : fixed_points (dumb_action' H)) :
  ∃ g, (𝒾 (normalizer H)) '' ((projection H) ⁻¹' {b}) = g ⋆ H :=
begin
  rcases b with ⟨⟨_, g, rfl⟩, hg⟩,
  use g,
  change to_lcosets g H ∈ _ at hg,
  rw foo at hg,
  ext x,
  split,
    rintro ⟨⟨k, hk⟩, hk2, rfl⟩,
    rw mem_preimage at hk2,
    rw mem_singleton_iff at hk2,
    unfold projection at hk2,
    unfold to_lcosets at hk2,
    rw subtype.mk_eq_mk at hk2,
    rw subtype.mk_eq_mk at hk2,
    rw ←hk2,
    use 1,
    use H.one_mem,
    rw group.mul_one,
    refl,
  rintro ⟨a, ha, rfl⟩,
  use g * a,
    apply subgroup.mul_mem _ hg,
    apply le_normalizer H,
    exact ha,
  split,
  rw mem_preimage,
  rw mem_singleton_iff,
    unfold projection,
    unfold to_lcosets,
    rw subtype.mk_eq_mk,
    rw subtype.mk_eq_mk,
    rw lagrange.lcoset_eq,
    convert ha,
    simp [group.mul_assoc],
  refl
end

--lemma card_eq_card_of_injective ()
lemma proj_fincard [fintype G] (H : subgroup G) (b : fixed_points (dumb_action' H)) :
  fincard' ((projection H) ⁻¹' {b}) = fincard' H :=
begin
  cases proj_eq_coset H b with g hg,
  rw @lagrange.eq_card_of_lcoset _ _ H g,
  have h := fincard.card_eq_image_of_injective (𝒾 (normalizer H)) injective_𝒾,
  rw ← hg,
  rw ← h
end


noncomputable instance boo36 [fintype G] (H : subgroup G) : fintype H := fintype.of_injective (𝒾 H) injective_𝒾

def ZZZ [fintype G] (H : subgroup G) := fincard.finsum_fibres (projection H)

def lcosets_to_sets  (H : subgroup G): lcosets H → { B | ∃ g : G, B = lcoset g H } := id

open_locale classical

noncomputable instance boo38 [fintype G] (H : subgroup G) : fintype (lcosets H) :=
fintype.of_surjective (λ g, to_lcosets g H) begin
  rintro ⟨C_val, g, rfl⟩,
  use g,
  refl
end


lemma card_subgroup_eq_card_carrier (H : subgroup G) : fincard' H = fincard' H.carrier := 
begin
  apply fincard.of_equiv,
  use [id, id];
  {intros x, refl}
end  

lemma zero_lt_card_subgroup [fintype G] (H : subgroup G): 0 < fincard' H  := 
begin
  suffices: fincard' H ≠ 0,
  exact nat.pos_of_ne_zero this,
  intro h,
  rw [card_subgroup_eq_card_carrier, fincard.card_eq_zero_iff H.carrier] at h,
  rw [← mem_empty_eq (1 : G), ← h],
  exact H.one_mem,
end 

lemma index_normalizer_congr_index_modp [fintype G] 
  {p : ℕ} (hp: p.prime) (H : subgroup G) (h: is_p_subgroup H p) :
  index' (normalizer_of_set (H : set G)) H ≡ index H [MOD p] := 
  begin
    have claim: ∀ g : G, to_lcosets g H ∈ (fixed_points (dumb_action' H)) ↔ g ∈ normalizer_of_set H.carrier,
      { intro g,
        rw normalizer_of_set_eq_normalizer,
        exact foo H g },
    have h2 : fincard'(fixed_points (dumb_action' H)) = (index' (normalizer_of_set (H : set G)) H),
      { cases h with n hn,
        unfold index',
        erw normalizer_of_set_eq_normalizer,
        rw ← fincard.finsum_fibres (projection H),
        simp_rw proj_fincard,
        rw ← finsum_in_eq_finsum (λ _, fincard' H),
        rw @finsum_const_nat _ _ _ (fincard' H),
        rw nat.mul_div_cancel,
        exact zero_lt_card_subgroup H,
        simp,
        apply_instance },
    have h3 : index H = fincard' (lcosets H),
      { unfold index,
        rw @lagrange.lagrange _ _ H,
        rw _root_.mul_comm,
        rw nat.mul_div_cancel,
          refl,
        exact zero_lt_card_subgroup H },
    have : index H ≡ (index' (normalizer_of_set (H : set G)) H) [MOD p],
      rw h3,
      rw ←h2,
      cases h with n hn,
      apply card_set_congr_card_fixed_points_mod_prime (dumb_action' H) _ hp n hn,  
    exact this.symm
  end    

lemma p_div_index_div_normalizer_of_set [fintype G](H : subgroup G) {p : ℕ} (hp: p.prime) (h: is_p_subgroup H p):
p ∣ index H → p ∣ (index' (normalizer_of_set (H : set G)) H):=
begin
  intro hH,
  have h1: index' (normalizer_of_set (H : set G)) H  ≡ H.index [MOD p],
    {apply index_normalizer_congr_index_modp hp H h},
  refine nat.modeq.modeq_zero_iff.mp _,
    apply nat.modeq.trans h1,
    apply nat.modeq.symm,
    apply nat.modeq.modeq_of_dvd,
    rw [int.coe_nat_zero, sub_zero],
    norm_cast,
    exact hH,
end  


lemma normalizer_neq_subgroup [fintype G] 
  (H : subgroup G) {p : ℕ} (hp: p.prime) (h: is_p_subgroup H p) : 
  p ∣ index H → normalizer_of_set (H : set G) ≠ H := 
begin
  intro hH,
  have h1: index' (normalizer_of_set (H : set G)) H  ≡ H.index [MOD p],
    { apply index_normalizer_congr_index_modp hp H h },
  have h2: p ∣ (index' (normalizer_of_set (H : set G)) H),
    { apply p_div_index_div_normalizer_of_set H hp h, assumption },
  have h3: (index' (normalizer_of_set (H : set G)) H) ≠ 1,
    { intro hfalse,
      rw hfalse at h2,
      exact nat.prime.not_dvd_one hp h2 },
  have h4: fincard' (normalizer_of_set (H : set G)) ≠ fincard' H,
    { unfold index' at h3,
      intro hfalse,
      rw hfalse at h3,
      apply h3,
      apply nat.div_self,
      apply zero_lt_card_subgroup },
  intro hfalse, 
  apply h4,
  rw hfalse, 
end  

lemma index_eq_card_quotient [fintype G] (H : normal G): index (H : subgroup G) = fincard' (G /ₘ H) := 
begin
  unfold index,
  rw lagrange.card_quotient_eq_mul H,
  change _ /fincard' H = _,
  rw nat.mul_comm,
  rw nat.mul_div_assoc,
  rw nat.div_self,
  rw nat.mul_one,
  apply zero_lt_card_subgroup,
  refl,
end  

noncomputable instance boo54 [fintype G] (N : normal G) : fintype (G /ₘ N) :=
fintype.of_surjective (quotient.mk N) begin
  exact quotient.is_surjective_mk
end

def equiv_comap_of_sub (K : subgroup G) (H : normal G)
  (h : H.to_subgroup ≤ K) : normal.comap (𝒾 K) H ≃ H := 
{ to_fun := λ g, ⟨g.1.1, 
    begin
      rcases g with ⟨⟨g, _⟩, hg⟩,
      exact hg
    end⟩,
  inv_fun := λ g, ⟨⟨g.1, h g.2⟩, g.2⟩,
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; simp,
  right_inv := by rintro ⟨_, _⟩; simp }

def equiv_comap_of_sub' (H K : subgroup G)
  (h : H ≤ K) : subgroup.comap (𝒾 K) H ≃ H := 
{ to_fun := λ g, ⟨g.1.1, 
    begin
      rcases g with ⟨⟨g, _⟩, hg⟩,
      exact hg
    end⟩,
  inv_fun := λ g, ⟨⟨g.1, h g.2⟩, g.2⟩,
  left_inv := by rintro ⟨⟨_, _⟩, _⟩; simp,
  right_inv := by rintro ⟨_, _⟩; simp }

def equiv_map_of_sub (H : subgroup G) (K : subgroup H) :
  map (𝒾 H) K ≃ K := 
{ to_fun := λ k,
    begin
      refine ⟨⟨k.1, _⟩, _⟩;
        rcases k with ⟨k, ⟨_, hk⟩, hk', rfl⟩,
        exact hk,
        exact hk',
    end,
  inv_fun := λ k, ⟨k.1, k, k.2, rfl⟩,
  left_inv := by rintro ⟨_, _, _, _⟩; simp,
  right_inv := by rintro ⟨_, _⟩; simp }

lemma index_eq_index' [fintype G] (H K : subgroup G) (h: K ≤ H):
  index (comap (𝒾 H) K) = index' H K :=
begin
  unfold index,
  unfold index',
  rw fincard.of_equiv (equiv_comap_of_sub' K H h)
end

lemma index'_eq_card_quotient [fintype G] (H : subgroup G) (K : normal H): 
  index' H (map (𝒾 H) K) = fincard' (H /ₘ K) :=
begin
  unfold index',
  have h := lagrange.card_quotient_eq_mul K,
  rw h,
  rw fincard.of_equiv (equiv_map_of_sub H ↑K),
  rw _root_.mul_comm,
  convert nat.mul_div_cancel _ _,
  exact zero_lt_card_subgroup _,
end


theorem sylow_one [fintype G] 
  {p m n: ℕ} {hp : p.prime}{hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m} : 
  ∀ (i ≤ n), ∃ H : subgroup G, fincard' H = p ^ i := 
begin
  intros i hin,
  induction i with i hi,   
  { use ⊥ ,
    rw nat.pow_zero,
    exact fincard_bot },
  rw nat.succ_eq_add_one at hin,
  have useful : 0 < n - i := nat.le_sub_left_of_add_le hin,
  have useful2 : i ≤ n,
    refine le_trans _ hin, simp,
  specialize hi useful2,
  cases hi with H hH,
  
  have fact0: p ∣ index H,
  { unfold index,
    rw [hG, hH, show n = i + (n - i), by simp [← nat.add_sub_assoc useful2 _], 
        nat.pow_add, nat.mul_assoc, nat.mul_comm, 
        nat.mul_div_assoc _ (show p ^ i ∣ p ^ i, by refl), 
        nat.div_self (nat.pow_pos (nat.prime.pos hp) i), 
        nat.mul_assoc, nat.mul_one],
    use p^(n - i - 1) * m, ring,
    rw nat.mul_assoc, congr,
    rw ← nat.pow_succ, congr,
    rw nat.succ_eq_add_one,
    generalize h : n - i = w,
    rw h at useful,
    refine (nat.sub_add_cancel _).symm,
    linarith },
  have fact1: index' (normalizer_of_set (H : set G)) H  ≡ H.index [MOD p],
  {  refine index_normalizer_congr_index_modp hp H _ ,
    use i, exact hH }, 
  have fact2: p ∣ (index' (normalizer_of_set (H : set G)) H),
  {  refine (p_div_index_div_normalizer_of_set H hp _ _),
    use i, exact hH, exact fact0},  
  have fact3: p ∣ fincard' (normalizer_of_set (H : set G) /ₘ normal_in_normalizer_of_set H),
    { rw ← index'_eq_card_quotient,
      cases fact2 with k hk,
      use k,
      rw ← hk, 
      unfold index',
      congr' 1,
      rw fincard.of_equiv (equiv_map_of_sub _ _),
      unfold normal_in_normalizer_of_set,
      convert fincard.of_equiv (equiv_comap_of_sub' _ _ _),
      rw normalizer_of_set_eq_normalizer,
      exact le_normalizer H
    },
  have fact4: ∃ (K : subgroup (normalizer_of_set (H : set G) /ₘ normal_in_normalizer_of_set H)), fincard' K = p,
    { refine @cauchy _ _ _ p hp fact3, },
  cases fact4 with K hK,
  have := quotient.quotient.comap_iso _ K,
  use map (𝒾 (normalizer_of_set H.carrier)) (quotient.quotient.comap (normal_in_normalizer_of_set H) K), 
  unfold map,
  rw card_subgroup_eq_card_carrier,
  simp,
  rw ← fincard.card_eq_image_of_injective (𝒾 (normalizer_of_set H.carrier)),
  change fincard' (quotient.quotient.comap (normal_in_normalizer_of_set H) K).carrier = p ^ i.succ,
  rw ←  card_subgroup_eq_card_carrier,
  rw @quotient.quotient.comap_card_eq _ _ _ (normal_in_normalizer_of_set H) K,
  rw hK,
  rw nat.pow_succ,
  congr,
  rw ← hH,
  apply fincard.of_equiv,
  refine equiv.trans (equiv_comap_of_sub _ _ _) _,
  { rintro h hh,
    unfold quotient.quotient.comap,
    rw mem_coe,
    rw mem_comap',
    convert K.one_mem,
    rw ← mem_kernel,
    rw quotient.kernel_mk,
    exact hh
  },
  { unfold normal_in_normalizer_of_set,
      convert (equiv_comap_of_sub' _ _ _),
    rw normalizer_of_set_eq_normalizer,
    exact le_normalizer H,
  },
  exact injective_𝒾,  
end    


def conjugate_iso (g : G) (H : subgroup G) : H ≅ conjugate_subgroup g H :=
{ to_fun := λ (h : H) , ⟨g * h * g⁻¹, begin use [h, h.2] end⟩,
  map_mul' := 
    begin
      rintro ⟨x, hx⟩ ⟨y, hy⟩,
      congr' 1,
      change g * (x * y) * g⁻¹ = _,
      simp [group.mul_assoc],   
    end,
  is_bijective := 
    begin
      split,
      {   intros x y hxy ,
        dsimp at *,
        cases y with y hy, 
        cases x with x hx, 
        rw subtype.mk_eq_mk at hxy,
        simpa using hxy,        
        },
      { unfold surjective,
        rintro ⟨b, h, hh, rfl⟩,
        use ⟨h, hh⟩, 
        simp }
    end }



lemma conjugates_eq_cardinality (g : G) (H : subgroup G) :
  fincard' H = fincard' (conjugate_subgroup g H) := 
fincard.of_equiv (group_hom.mul_equiv_of_iso (conjugate_iso g H)).to_equiv
  
/-def is_sylow_p_subgroup [fintype G] {p m n: ℕ} {hp : p.prime}{hG : fincard' G = p ^ n * m}
 {hdiv : ¬ p ∣ m} (K : subgroup G): Prop := fincard' K = p ^ n-/

-- theorem sylow_two [fintype G]{p : ℕ} {hp : p.prime} (H K : subgroup G) (h₁ : is_sylow_p_subgroup H hp)(h₂ : is_sylow_p_subgroup K hp) : 
-- ∃ (g : G), H = conjugate_subgroup g K  := sorry  


-- Consider the action of K on the set X of cosets of H in G μ: K × X → X, (y, xH) ↦ yxH. 
--Consider the points fixed by the action. Notice that since H is a Sylow p subgroup then p does not divide 
--fincard' X = index H, hence fincard'(fixed points μ ) ≠ 0. We then want to show that xH ∈ fixed_points μ 
--implies that the conjugate of K by x is a subgroup of H. Since conjugates are isomorphic they have the same cardinality.
--Hence x K x⁻¹ = H.



--Define the number of Sylow p-subgroups of G. 
-- noncomputable def number_sylow_p (G : Type) [group G] {p : ℕ} (hp : p.prime) := 
-- fincard' {K : subgroup G // is_sylow_p_subgroup K hp}

-- theorem sylow_three_part1 [fintype G]{p m n: ℕ}{hp : p.prime}
--   {hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m}:
-- number_sylow_p G hp ≡ 1 [MOD p] := sorry 
-- theorem sylow_three_part2 [fintype G]{p m n: ℕ} {hp : p.prime}{hG : fincard' G = p ^ n * m} {hdiv : ¬ p ∣ m}:
-- number_sylow_p G hp ∣ m := sorry 
--By Sylow 1 ∃ a Sylow p-subgroup P, so we set X = Sylp(G) = {Sylow p-groups in G}
--Then P acts on X by μ : P × X → X, (x, Q) ↦ xQx⁻¹ (this is what we defined conjugate_action to be)
--By card_set_congr_card_fixed_points_mod_prime we have
-- number_sylow_p = fincard' X ≡ fincard' (fixed points μ) [MOD p]. Want to show fincard' (fixed points μ) = 1.
--Let P ∈ fixed points μ and Q ∈ fixed points μ. Then P is a subgroup of normalizer_of_set Q
--Both P and Q are Sylow p-subgroups of normalizer_of_set Q, so ∃ x ∈ normalizer_of_set Q s.t. xQx⁻¹ = P (Sylow 2)
--By def of normalizer_of_set Q we have Q = P, so fixed_points μ = {P}, proving the first part of the theorem.end
--Now if P acts on X by conjugation ∃ ! orbit such that X = orbit G P (Sylow 2).
--By orbit-stabilizer number_sylow_p = (fincard' X) ∣ (fincard' G)=p^n *m which implies it divides m.

end mygroup
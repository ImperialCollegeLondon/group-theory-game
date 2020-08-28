import orbit.orbit_stabilizer





def normalizer' [group G] (H : subgroup G) :=
 stabilizer (conjugation_action) H
 

lemma mem_normalizer'_def [group G] {H : subgroup G} (x : G) :
  x ∈ normalizer' H ↔ {k : G | ∃ (h : G) (H : h ∈ H), k = x * h * x⁻¹} = H := subgroup.ext'_iff.symm

lemma mem_normalizer'_iff [group G] {H : subgroup G} (x : G):
  x ∈ normalizer' H ↔ ∀ k : G, k ∈ H ↔ x * k * x⁻¹ ∈ H := 
begin
  rw mem_normalizer'_def,
  split,
  {  intros hx s,
    rw ext_iff at hx,
    specialize hx s⁻¹,
    dsimp at hx,
    rw mem_coe' at hx,
    rw inv_mem_iff at hx,
    rw ← hx,
    clear hx,
    split,
     {rintro ⟨h, hh, hs⟩,
      
      
      },
     {sorry} 
    
  },

  {sorry},  
  /-have test: s⁻¹ ∈ H ,
   apply H.inv_mem hs,
  have: x⁻¹ * s * x = w,
    apply group.mul_left_cancel x,
    rw ← group.mul_assoc,
    rw ← group.mul_assoc,
    rw group.mul_right_inv,
    rw group.one_mul,
    apply group.mul_right_cancel x⁻¹,
    rw group.mul_assoc,
    rw group.mul_right_inv,
    rw group.mul_one,
    assumption,-/
  


end  


lemma normalizer_eq_stabilizer'' [group G] (H : subgroup G) : 
(normalizer' H  : set G) = {g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H} := 
begin
   ext1,
   rw subgroup.mem_coe',
   rw mem_normalizer'_def,
   rw ext_iff,
   split,
   intro h,
   sorry
end



lemma normalizer_eq_stabilizer' [group G] (H : subgroup G) : 
(normalizer' H  : set G) = {g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H} := 
begin
   ext1,
   split,
    intro hx,
    dsimp at *,
    intro n,
    split, 
      intro hn,
      unfold_coes at hx,
      unfold normalizer' at hx,
      unfold stabilizer at hx,
      unfold conjugation_action at hx,
      unfold conjugate_subgroup at hx,
      simp at *,
      rw ← hx,
      rw ← subgroup.mem_coe,
      dsimp,
      use n,
      split,
      exact hn,
      refl,

  intro hxn,
  unfold_coes at hx,
  unfold normalizer' at hx,
  unfold stabilizer at hx,
  unfold conjugation_action at hx,
  unfold conjugate_subgroup at hx,
  simp at *,
  

      
  sorry

end  


lemma index_normalizer_congr_index_modp [fintype G]{p : ℕ} (hp: p.prime) (H : subgroup G) (h: is_p_subgroup H p):
  (index' (normalizer (H : set G)) H ) ≡ (index H) [MOD p] := sorry

lemma normalizer_neq_subgroup [fintype G](H : subgroup G){p : ℕ}(hp: p.prime)(h: is_p_subgroup H p) :
 p ∣ (index H) → normalizer (H : set G)  ≠ H := sorry


theorem sylow_one_part1 [fintype G] {p m n: ℕ}{hp : p.prime} {hG : fincard' G = p^n * m} {hdiv : ¬ p ∣ m}:
∀ (i ≤ n), ∃ (H : subgroup G), fincard' H = p^i := sorry
-- and want to write that each of these subgroups of cardinality p^i is normal in a subgroup of cardinality p^(i+1)

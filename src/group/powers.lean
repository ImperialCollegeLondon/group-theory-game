import group.basic
import int.iterate

namespace mygroup

namespace group

variables {G : Type} [group G]

open int 

/-- left multiplication is a bijection-/
def lmul (g : G) : G ≃ G :=
{ to_fun := (*) g, inv_fun := (*) g⁻¹,
  left_inv := begin intro x, rw [←mul_assoc, mul_left_inv, one_mul], end,
  right_inv := begin intro x, rw [←mul_assoc, mul_right_inv, one_mul] end }

def pow : G → ℤ → G :=
  λ g n, (iterate n (lmul g)) 1

instance : has_pow G ℤ := ⟨pow⟩

variables (n m : ℤ) (g h k : G)

lemma lmul_one : (lmul g) 1 = g := mul_one g

lemma lmul_symm  : (lmul g).symm = lmul g⁻¹ := by ext; refl
lemma lmul_symm' : (lmul g)⁻¹ = (lmul g).symm := rfl

lemma pow_def     : g ^ n = iterate n (lmul g) 1 := rfl 
lemma pow_one_mul : iterate 1 (lmul g) h = g * h := rfl

@[simp] lemma pow_zero : g ^ (0 : ℤ) = 1 := rfl
@[simp] lemma pow_one  : g ^ (1 : ℤ) = g := 
begin
  rw [pow_def, iterate.one],
  exact mul_one g, 
end

theorem pow_neg : g ^ -n = g⁻¹ ^ n :=
by rw [pow_def, pow_def, ←lmul_symm, ←iterate.neg]

-- A direct corollary
@[simp] theorem pow_neg_one_inv (g : G) : g ^ (-1 : ℤ) = g⁻¹ := by simp [pow_neg 1 g]

lemma iterate_succ : iterate (n + 1) (lmul g) h = g * iterate n (lmul g) h := 
by rw [add_comm, ←iterate.comp, pow_one_mul]

lemma iterate_mul_assoc : (iterate n (lmul g) h) * k = iterate n (lmul g) (h * k) :=
begin
  apply int.induction_on' n 0,
    { refl },
    { intros _ _ h,
      rw [iterate_succ, mul_assoc, h, ←iterate_succ] },
    { intros m _ h,
      rw [show m - 1 = -(-m + 1), by ring],
      rw [iterate.neg, lmul_symm, iterate_succ, mul_assoc,
          ←lmul_symm, ←iterate.neg, neg_neg, h, lmul_symm, 
          iterate_succ, ←lmul_symm, ←iterate.neg, neg_neg] }
end

lemma pow_mul_eq_iterate (n : ℤ) : g ^ n * k = iterate n (lmul g) k :=
by convert iterate_mul_assoc n g 1 k; exact (one_mul _).symm

theorem pow_add : g ^ (m + n) = g ^ m * g ^ n :=
begin
  iterate 3 { rw pow_def },
  rw [←iterate.comp, iterate_mul_assoc, one_mul]
end

theorem pow_sub : g ^ (m - n) = g ^ m * g ^ (-n) :=
by rw [sub_eq_add_neg, pow_add]

theorem pow_mul : g ^ (m  * n) = (g ^ n) ^ m :=
begin
  simp [pow_def],
  rw [←iterate.mul _ _ _ g], 
  congr, ext,
  show _ = (n.iterate (lmul g)) 1 * x,
  rw [iterate_mul_assoc, one_mul],
end

theorem pow_inv : (g ^ n)⁻¹ = g⁻¹ ^ n :=
begin
  apply int.induction_on n,
  { simp },
  { intros i hi,
    rw [pow_add, pow_one, inv_mul, hi, add_comm, pow_add, pow_one] },
  { intros i hi,
    rw [pow_sub, sub_eq_add_neg, add_comm, pow_add, pow_neg, pow_neg, pow_one,
      inv_mul, inv_inv, ←pow_neg i, hi, pow_neg 1, inv_inv, pow_one] },  
end

@[simp] lemma one_pow : (1 : G) ^ n = 1 := 
begin
  apply int.induction_on n,
    { exact pow_zero 1 },
    { intros i hi, rw [pow_add, hi, pow_one, one_mul] },
    { intros i hi, rw [sub_eq_add_neg, pow_add, hi, one_mul, pow_neg, pow_one, one_inv] }
end

theorem mul_pow {H : Type} [hH :comm_group H] {g h : H} : 
  g ^ n * h ^ n = (g * h) ^ n := 
begin
  rw [pow_def, pow_def, pow_def, iterate_mul_assoc, one_mul],
  apply int.induction_on' n 0,
    { simp },
    { intros k hk _ ,
      repeat { rw iterate_succ },
      rw [← a, ← iterate_mul_assoc],
      simp [← pow_mul_eq_iterate, mul_assoc, hH.mul_comm, hH.mul_comm, mul_assoc] },
    { intros k hk _,
      cases (show ∃ m : ℤ, m + 1 = k, by exact ⟨k - 1, by norm_num⟩) with m hm,    
      rw ← hm at *,
      repeat { rw iterate_succ at a },
      rw [← add_sub, sub_self, add_zero],       
      simp [← pow_mul_eq_iterate, mul_assoc, hH.mul_comm] at *,
      apply mul_left_cancel'' h,
      rw [← a, hH.mul_comm],
      simp [hH.mul_comm, mul_assoc] }
end  

end group

end mygroup
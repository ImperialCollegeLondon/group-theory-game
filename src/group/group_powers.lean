import group.theorems
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


def pow : ℤ → G → G :=
  λ n g, (iterate n (lmul g)) 1

-- binding power is a joke
notation `⦃`:91 n `⦄^`:91 g :91 := pow n g
-- Why do you force me to use this awful notation instead of making a has_pow
-- instance :(

variables (n m : ℤ) (g h k : G)

lemma lmul_one : (lmul g) 1 = g := mul_one g

lemma lmul_symm  : (lmul g).symm = lmul g⁻¹ := by ext; refl
lemma lmul_symm' : (lmul g)⁻¹ = (lmul g).symm := rfl

lemma pow_def     : ⦃n⦄^g = iterate n (lmul g) 1 := rfl 
lemma pow_one_mul : iterate 1 (lmul g) h = g * h := rfl

@[simp] lemma zero_pow : ⦃0⦄^g = 1 := rfl
@[simp] lemma one_pow  : ⦃1⦄^g = g := 
begin
  rw [pow_def, iterate.one],
  exact mul_one g, 
end

theorem pow_neg : ⦃-n⦄^g = ⦃n⦄^g⁻¹ :=
by rw [pow_def, pow_def, ←lmul_symm, ←iterate.neg]

-- A direct corollary
@[simp] theorem pow_neg_one_inv (g : G) : ⦃-1⦄^g = g⁻¹ := by simp [pow_neg 1 g]

lemma iterate_succ : iterate (n + 1) (lmul g) h = g * iterate n (lmul g) h := 
by rw [add_comm, ←iterate.comp, pow_one_mul]

-- What this is saying is essentially (g^n * h) * k = g^n * (h * k)
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

lemma pow_mul_eq_iterate (n : ℤ) : ⦃n⦄^g * k = iterate n (lmul g) k :=
begin
  unfold pow,
  rw [iterate_mul_assoc n g 1 k, one_mul],
end

theorem pow_add : ⦃m + n⦄^g = ⦃m⦄^g * ⦃n⦄^g :=
begin
  iterate 3 { rw pow_def },
  rw [←iterate.comp, iterate_mul_assoc, one_mul]
end

theorem pow_sub : ⦃m - n⦄^g = ⦃m⦄^g * ⦃-n⦄^g :=
begin
  rw sub_eq_add_neg,
  rw pow_add,
end


theorem pow_mul : ⦃m * n⦄^g = ⦃m⦄^⦃n⦄^g :=
begin
  simp [pow_def],
  rw [←iterate.mul _ _ _ g], 
  congr, ext,
  show _ = (n.iterate (lmul g)) 1 * x,
  rw [iterate_mul_assoc, one_mul],
end


theorem pow_inv : (⦃n⦄^g)⁻¹ = ⦃n⦄^g⁻¹ :=
begin
  apply int.induction_on n,
  { simp },
  { intros i hi,
    rw [pow_add, one_pow, inv_mul, hi, add_comm, pow_add, one_pow],
  },
  { intros i hi,
    rw [pow_sub, sub_eq_add_neg, add_comm, pow_add, pow_neg, pow_neg, one_pow,
      inv_mul, inv_inv, ←pow_neg i, hi, pow_neg 1, inv_inv, one_pow],
  },  
end

@[simp] lemma pow_one (n : ℤ) : ⦃n⦄^(1 : G) = 1 := 
begin
  apply int.induction_on n,
    { exact zero_pow 1 },
    { intros i hi, rw [pow_add, hi, one_pow, one_mul] },
    { intros i hi, rw [sub_eq_add_neg, pow_add, hi, one_mul, pow_neg, one_pow, one_inv] }
end

-- Is this useful? Only true in abelian group
theorem mul_pow {H : Type} [hH :comm_group H] {g : H} {h : H} : 
  ⦃n⦄^g * ⦃n⦄^h = ⦃n⦄^(g * h) := 
begin
  rw [pow_def, pow_def, pow_def, iterate_mul_assoc, one_mul],
  apply int.induction_on' n 0,
    { simp },
    { intros k hk _ ,
      repeat {rw iterate_succ},
      rw [← a, ← iterate_mul_assoc],
      simp [←pow_mul_eq_iterate, mul_assoc, hH.mul_comm, hH.mul_comm, mul_assoc] },
    { intros k hk _,
      cases (show ∃ m : ℤ, m + 1 = k, by exact ⟨k - 1, by norm_num⟩) with m hm,    
      rw ← hm at *,
      repeat {rw iterate_succ at a},
      rw [← add_sub, sub_self, add_zero],       
      simp [←pow_mul_eq_iterate, mul_assoc, hH.mul_comm] at *,
      apply mul_left_cancel'' h,
      rw [← a, hH.mul_comm],
      simp [hH.mul_comm, mul_assoc] }
end  

end group

end mygroup
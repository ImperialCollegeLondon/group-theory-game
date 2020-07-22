import group.theorems
import int.iterate

namespace mygroup

namespace group

variable {G : Type}
variable [group G]

namespace group

/-- left multiplication is a bijection-/
def lmul (g : G) : G ≃ G :=
{ to_fun := (*) g,
  inv_fun := (*) g⁻¹,
  left_inv := begin intro x, rw [←mul_assoc, mul_left_inv, one_mul], end,
  right_inv := begin intro x, rw [←mul_assoc, mul_right_inv, one_mul] end }

def pow : ℤ → G → G :=
λ n g, (int.iterate n (lmul g)) 1

-- binding power is a joke
notation `⦃`:91 n `⦄^`:91 g := pow n g


@[simp] lemma zero_pow (g : G) : (⦃0⦄^g : G)= 1 := rfl

@[simp] lemma neg_one_pow_inv (g : G) : (⦃-1⦄^g : G) = g⁻¹ :=
begin
  simp [pow, int.iterate],
  have h : ∀ e : G ≃ G, e⁻¹ = e.symm := by intro e; refl,--equiv.perm.inv_def,
  rw h,
  simp [lmul]
end

variables (n : ℤ) (g h k : G)

open int.iterate int

lemma pow_def : (⦃n⦄^g : G) = int.iterate n (lmul g) 1 := rfl

lemma mul : g * h = int.iterate 1 (lmul g) h := rfl

lemma foo : (iterate n (lmul g) h) * k = iterate n (lmul g) (h * k) :=
begin
  -- this is I think what we need
  sorry
end

@[simp] lemma pow_add_mul {g : G} {m n : ℤ} : (⦃m+n⦄^g : G) = (⦃m⦄^g) * ⦃n⦄^g :=
begin
  rw pow_def,
  rw pow_def,
  rw pow_def,
  rw ←comp,
  rw foo,
  rw one_mul
end

-- lemma pow_mul : (⦃n⦄^g : G) * h = int.iterate n (lmul g) h :=
-- begin
--   change int.iterate n (lmul g) 1 * h = int.iterate n (lmul g) h, 
--   rw mul,
--   rw int.iterate.one,
--   refl,
-- end


private lemma succ_pow {g : G} {n : ℤ} : (⦃n + 1⦄^g : G) = ⦃n⦄^g * g := 
begin
  unfold pow,

end



#exit
--@[simp] lemma pow_int_of_nat {g : G} {n : ℕ} : g ^ (int.of_nat n) = g ^ n := rfl
--@[simp] lemma pow_neg {g : G} {n : ℕ} : g ^ (-[1+ n]) = (g ^ (n + 1))⁻¹ := rfl
--@[simp] theorem pow_neg_succ (g : G) (n : ℕ) : g ^ -[1+n] = (g ^ n.succ)⁻¹ := rfl

--@[simp] lemma zero_pow_nat {g : G} : g ^ 0 = 1 := rfl

--@[simp] lemma succ_pow_nat {g : G} {n : ℕ} : g ^ (n + 1) = g ^ n * g := rfl



-- @[simp] lemma succ_pow {g : G} {n : ℤ} : g ^ (n + 1) = g ^ n * g := 
-- begin
  
--     induction n,
--         {rw [pow_int_of_nat, ←succ_pow_nat], refl},
--         sorry
-- end

--@[simp] lemma one_mul_pow_nat {g : G} {n : ℕ} : 1 * (g ^ n) = (g ^ n) := by {simp}

--@[simp] lemma pow_mul_one_nat {g : G} {n : ℕ} : (g ^ n) * 1 = (g ^ n) := by{simp}

--@[simp] lemma pow_add_mul_nat {g : G} {m n : ℕ} : g ^ (m + n) = g ^ m * g ^ n :=
--begin
--    induction n with k hk,
--        {rw [add_zero, zero_pow_nat, pow_mul_one_nat]},
--        rwa [succ_pow_nat, ←mul_assoc, ←hk, ←succ_pow_nat, nat.add_assoc]
--end

-- @[simp] lemma pow_add_mul {g : G} {m n : ℤ} : g ^ (m + n) = g ^ m * g ^ n :=
-- begin
--     induction n,
--     induction m,
--         {repeat {rw pow_int_of_nat}, rw ←pow_add_mul_nat, refl},
--         repeat {sorry}
-- end

@[simp] lemma inv_pow {g : G} {n : ℕ} : (g ^ n)⁻¹ = g⁻¹ ^ n :=
begin
    sorry
end

@[simp] lemma pow_mul_pow_nat {g : G} {m n : ℕ} : g ^ (m * n) = (g ^ m) ^ n :=
begin
    induction n with k hk,
        simp only [nat.nat_zero_eq_zero, zero_pow_nat, mul_zero],
        show g ^ (m * k + m) = (g ^ m) ^ (k + 1),
        rw [succ_pow_nat, ←hk, pow_add_mul_nat]
end

@[simp] lemma pow_mul_pow {g : G} {m n : ℤ} : g ^ (m * n) = (g ^ m) ^ n :=
begin
    sorry
end

end group

end mygroup
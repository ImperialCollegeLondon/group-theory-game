import group.level01_extended

namespace mygroup

namespace group

variable {G : Type}
variable [group G]

@[simp] lemma pow_int_of_nat {g : G} {n : ℕ} : g ^ (int.of_nat n) = g ^ n := rfl
@[simp] lemma pow_neg {g : G} {n : ℕ} : g ^ (-[1+ n]) = g⁻¹ ^ (n + 1) := rfl

@[simp] lemma zero_pow_nat {g : G} : g ^ 0 = 1 := rfl
@[simp] lemma zero_pow {g : G} : g ^ (0 : ℤ) = 1 := rfl

@[simp] lemma succ_pow_nat {g : G} {n : ℕ} : g ^ (n + 1) = g ^ n * g := rfl

@[simp] lemma neg_one_pow_inv {g : G} : g ^ (-1 : ℤ) = g⁻¹ := 
begin
    have : -1 = -[1+ 0] := rfl,
    rw [this, pow_neg, nat.add_comm, succ_pow_nat],
    simp only [mygroup.group.mul_left_eq_self, mygroup.group.zero_pow_nat]
end

@[simp] lemma succ_pow {g : G} {n : ℤ} : g ^ (n + 1) = g ^ n * g := 
begin
    induction n,
        {rw [pow_int_of_nat, ←succ_pow_nat], refl},
        rw [pow_neg, succ_pow_nat, mul_assoc, mul_left_inv, mul_one],
        sorry
end

@[simp] lemma one_mul_pow_nat {g : G} {n : ℕ} : 1 * (g ^ n) = (g ^ n) := by {simp}

@[simp] lemma pow_mul_one_nat {g : G} {n : ℕ} : (g ^ n) * 1 = (g ^ n) := by{simp}

@[simp] lemma pow_add_mul_nat {g : G} {m n : ℕ} : g ^ (m + n) = g ^ m * g ^ n :=
begin
    induction n with k hk,
        {rw [add_zero, zero_pow_nat, pow_mul_one_nat]},
        rwa [succ_pow_nat, ←mul_assoc, ←hk, ←succ_pow_nat, nat.add_assoc]
end

@[simp] lemma pow_add_mul {g : G} {m n : ℤ} : g ^ (m + n) = g ^ m * g ^ n :=
begin
    induction n,
    induction m,
        {repeat {rw pow_int_of_nat}, rw ←pow_add_mul_nat, refl},
        repeat {sorry}
end

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
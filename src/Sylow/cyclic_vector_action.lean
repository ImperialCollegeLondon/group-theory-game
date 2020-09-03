-- action of cyclic n.succ on lists of length n.succ
-- whose product is 1

import Sylow.prod_eq_one

namespace mygroup

variables (G : Type) [group G] (n : ℕ)

def cycle : {v : fin n.succ → G // finmap.prod_eq_one v} ≃ {v : fin n.succ → G // finmap.prod_eq_one v} :=
{ to_fun := λ f, ⟨f.1 ∘ fin.S.succ, finmap.prod_eq_one_succ f.2⟩,
  inv_fun := λ f, ⟨f.1 ∘ (⦃(n : ℤ)⦄^(fin.S.succ) : fin n.succ ≃ fin n.succ), finmap.prod_eq_one_iterate n f.2⟩,
  left_inv := λ f, begin
    cases f with v hv,
    ext x,
    simp,
    congr',
    convert fin.S.succ.pow_n n x
  end,
  right_inv := λ f, begin
    cases f with v hv,
    ext x,
    simp,
    congr',
    change (_ * (fin.S.succ)) x = _,
    convert fin.S.succ.pow_n n x using 1,
    apply congr_fun,
    simp,
    rw group.pow_add,
    rw group.one_pow,
    refl
  end }

lemma cycle_pow_aux (d : ℕ) (v : fin n.succ → G) (hv : v ∈ @finmap.prod_eq_one G _ n.succ)
  (x : fin n.succ):
  ((⦃(d : ℤ)⦄^cycle G n : _ ≃ _).to_fun ⟨v, hv⟩).1 x =
  v ((⦃(d : ℤ)⦄^(fin.S.succ' n : _ ≃ _)) x) :=
begin
  revert x,
  induction d with e he,
  { simp },
  { intro x,
    simp_rw nat.succ_eq_add_one,
    rw int.coe_nat_add,
    conv_lhs {rw add_comm},
    --rw add_comm,
    rw group.pow_add,
    rw int.coe_nat_one,
    rw group.one_pow,
    rw group.pow_add,
    rw group.one_pow,
    simp,
    rw ←he,
    simp,
    refl }
end


lemma cycle_pow_n_succ : ⦃n.succ⦄^(cycle G n) = equiv.refl _ :=
begin
  ext i,
  cases i with v hv,
  simp,
  have h := fin.S.succ.pow_n n x,
  apply_fun v at h,
  convert h,
  simp,
  unfold_coes,
  simp,
  apply cycle_pow_aux
end

end mygroup

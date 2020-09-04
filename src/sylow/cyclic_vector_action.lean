-- action of cyclic n.succ on lists of length n.succ
-- whose product is 1

import sylow.prod_eq_one

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

def cool_thing : cyclic (n.succ : ℕ) →* _ :=
  to_hom_cyclic (cycle G n) n.succ (cycle_pow_n_succ G n)

def cool_action : laction (cyclic n.succ) {v // finmap.prod_eq_one v} :=
laction_eq_hom.symm (cool_thing G n)

-- need to know the size of {v // finmap.prod_eq_one v}
-- and we do this by showing it's equiv to `fin n → G`

lemma fixed_point_const (v : fixed_points (cool_action G n)) (i : fin n.succ ):
v.1.1 i = v.1.1 ⟨0, nat.zero_lt_succ n⟩ :=
begin
  cases i with i hi,
  have h := v.2 (quotient.mk (mod n.succ) (i : ℤ)),
  unfold cool_action cool_thing laction_eq_hom to_hom_cyclic at h,
  simp at h,
  rw mygroup.quotient.lift_mk at h,
  unfold order_map at h,
  unfold_coes at h,
  simp at h,
  rw subtype.ext_iff at h,
  replace h := congr_fun h ⟨0, nat.zero_lt_succ n⟩,
  convert h using 1,
  convert (cycle_pow_aux G n i v.1.1 v.1.2 ⟨0, nat.zero_lt_succ n⟩).symm,
  swap, ext x, refl,
  rw fin.S.succ.pow_k,
  ext,
  rw fin.val_add,
  unfold has_add.add fin.add,
  rw fin.coe_val_of_lt hi,
  simp,
  exact (nat.mod_eq_of_lt hi).symm
end

-- lemma list.repeat_nth_le (α : Type) (a : α) (n i : ℕ) (h : i < n) :
--   (list.repeat a n).nth_le i (begin convert h, simp, end) = a :=
-- begin
--   apply list.nth_le_repeat
-- end

/-
i: fin n.succ
⊢ (list.repeat (v.val.val ⟨0, _⟩) n.succ).nth_le i.val _ = v.val.val ⟨0, _⟩
-/
lemma fixed_point_eq_repeat (v : fixed_points (cool_action G n)) :
  list.of_fn v.1.1 = list.repeat (v.1.1 ⟨0, nat.zero_lt_succ n⟩) n.succ :=
begin
  apply @list.ext' n.succ,
  { intros i,
    convert fixed_point_const G n v i,
    simp, 
    { rw list.nth_le_repeat },
    simp,
    simp },
end


lemma fixed_point_pow (v : fixed_points (cool_action G n)) :
⦃n.succ⦄^(v.1.1 ⟨0, nat.zero_lt_succ n⟩) = 1 :=
begin
  have h := v.2,
  have h2 := v.1.2,
  convert h2,
  unfold finmap.prod_eq_one at h2,
  rw ←list.prod_repeat',
  congr',
  rw ←fixed_point_eq_repeat,
  simp
end

def fixed_points_eq_roots : fixed_points (cool_action G n) ≃ {g : G // ⦃n.succ⦄^g = 1} :=
{ to_fun := λ f, ⟨f.1.1 ⟨0, nat.zero_lt_succ n⟩, begin
    apply fixed_point_pow
  end⟩,
  inv_fun := λ g, ⟨⟨λ _, g.1, begin
    unfold finmap.prod_eq_one,
--    rw ←g.2,
    convert list.prod_repeat' n.succ g.1,
    swap, exact g.2.symm,
    apply @list.ext' n.succ;
    [skip, simp, simp],
    intro i,
    rw list.nth_le_repeat,
    simp
  end⟩, begin
    rw mem_fixed_points_iff_stabilizer_univ,
    rw eq_top_iff,
    rw ← cyclic.generator_generates,
    rw subgroup.closure_le,
    show _ ⊆ _,
    rw set.singleton_subset_iff,
    rw subgroup.mem_coe',
    rw laction.mem_stabilizer,
    cases g with g hg,
    simp,
    ext,
    refl
  end⟩,
  left_inv := begin
    intro f,
    simp,
    ext i,
    exact (fixed_point_const G n f i).symm,
  end,
  right_inv := begin
    intro g,
    simp
  end }
end mygroup

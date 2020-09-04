-- we compute the cardinality of the vectors of length n.succ
-- whose product is 1

import sylow.prod_eq_one

namespace mygroup

variables (G : Type) [group G] (n : ℕ)

/-- Given a vector `v` of length `n`, make a vector of length `n+1` whose product is `1`,
by consing the the inverse of the product of `v`. -/
@[reducible] def finmap.to_succ (v : fin n → G) :
fin (n.succ) → G := λ i, if h : i.1 < n then v ⟨i.1, h⟩ else ((list.of_fn v).prod')⁻¹

def finmap.to_succ.prod_eq_one (v : fin n → G) :
  finmap.prod_eq_one (finmap.to_succ G n v) :=
begin
  unfold finmap.prod_eq_one,
  rw vector.to_list.succ',
  rw list.prod_append',
  rw list.prod_singleton',
  unfold finmap.to_succ,
  simp,
  convert group.mul_right_inv ((list.of_fn v).prod'),
  ext i,
  rw dif_pos i.2
end

lemma finmap.to_succ_injective (n : ℕ) :
  function.injective (finmap.to_succ G n) :=
λ v w h,
begin
  ext m,
  unfold finmap.to_succ at h,
  replace h := congr_fun h ⟨m.1, lt_trans m.2 (nat.lt_succ_self n)⟩,
  simp at h,
  rw dif_pos m.2 at h,
  rwa dif_pos m.2 at h,
end

lemma finmap.last_eq_inv_prod (v : fin n.succ → G) (hv : finmap.prod_eq_one v) :
v ⟨n, nat.lt_succ_self n⟩ = ((list.of_fn
  (λ i, v ⟨i.1, lt_trans i.2 (nat.lt_succ_self n)⟩ : fin n → G)).prod')⁻¹ :=
begin
  unfold finmap.prod_eq_one at hv,
  rw [vector.to_list.succ', list.prod_append', list.prod_singleton'] at hv,
  replace hv := group.eq_inv_mul_of_mul_eq hv,
  rw group.mul_one at hv,
  convert hv, simp,
  ext i,
  simp,
  congr'
end


def prod_eq_one_equiv : {v : fin n.succ → G // finmap.prod_eq_one v} ≃ (fin n → G) :=
{ to_fun := λ v i, v.1 ⟨i.1, lt_trans i.2 (nat.lt_succ_self n)⟩,
  inv_fun := λ v, ⟨finmap.to_succ G n v, finmap.to_succ.prod_eq_one G n v⟩,
  left_inv := λ v, begin
    cases v with v hv,
    ext i,
    simp,
    cases i with i his,
    unfold finmap.to_succ,
    by_cases hi : i < n,
    { rw dif_pos hi },
    rw dif_neg hi,
    rw nat.lt_succ_iff_lt_or_eq at his,
    cases his with his hin, contradiction,
    symmetry' at hin,
    subst hin,
    convert (finmap.last_eq_inv_prod G n v hv).symm
  end,
  right_inv := begin
    intro v,
    ext i,
    unfold finmap.prod_eq_one,
    unfold finmap.to_succ,
    simp,
    rw dif_pos i.2
  end
}

open_locale classical

noncomputable instance (X : Type) [fintype X] (Y : Type) [fintype Y] : fintype (X → Y) :=
by apply_instance

lemma card_function (X : Type) [fintype X] (Y : Type) [fintype Y] :
  fincard (X → Y) = fincard Y ^ fincard X :=
begin
  rw ← fincard.card_eq_fincard,
  rw ← fincard.card_eq_fincard,
  rw ← fincard.card_eq_fincard,
  convert fintype.card_fun,
end


noncomputable instance foo2 [fintype G] : fintype {v : fin n.succ → G // finmap.prod_eq_one v} :=
begin
  exact fintype.of_equiv (fin n → G) (prod_eq_one_equiv G n).symm
end

lemma card_cool_set [fintype G] :
  fincard {v : fin n.succ → G // finmap.prod_eq_one v} = fincard G ^ n :=
begin
  rw fincard.of_equiv (prod_eq_one_equiv G n),
  rw card_function,
  congr',
  rw ←fincard.card_eq_fincard,
  simp,
end


-- NEED TO COUNT.

-- todo : card (vector G n) = |G|^n

end mygroup


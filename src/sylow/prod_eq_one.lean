import data.zmod.basic subgroup.cyclic data.vector2

-- Lists of n elements of a group whose product is 1

-- lists will be modelled as functions `fin n → M` with (n : ℕ)
-- and M a group (or a monoid)

-- In this file I am going to define a predicate `prod_eq_one`
-- on `fin n → M`, and I am going to define a bijection `S`
-- of `fin n → M` (in fact an `equiv`) and I'm going to show
-- that its n'th power is 1.

/-! ## equiv stuff : stuff which is "the same". -/
def fin.to_zmod {n : ℕ} (a : fin n.succ) : zmod n.succ := a
def zmod.to_fin {n : ℕ} (a : zmod n.succ) : fin n.succ := a

-- if we are only thinking of ℕ as an ordered set then these ideas are "the same"
def fin.equiv_zmod {n : ℕ} : fin n.succ ≃ zmod n.succ := equiv.refl _

def zmod.S {m : ℕ} : zmod m ≃ zmod m := 
  ⟨λ n, n + 1, λ n, n - 1, by { intro _, simp }, by { intro _, simp }⟩

lemma list.ext' {n : ℕ} {α : Type} {L M : list α} (hL : L.length = n)
  (hM : M.length = n) (hLM : ∀ (i : fin n),
    L.nth_le i.1 (hL.symm ▸ i.2) = M.nth_le i.1 (hM.symm ▸ i.2)) : L = M :=
begin
  suffices : (⟨L, hL⟩ : vector α n) = ⟨M, hM⟩,
    exact subtype.mk.inj this,
  exact vector.ext (λ i, hLM i),
end

lemma vector.to_list.succ (n : ℕ) (M : Type) (v : vector M n.succ) :
v.to_list = v.nth 0 :: list.of_fn
  (λ (i : fin n), v.nth i.succ : fin n → M) :=
begin
  have h1 : v.to_list.length = n.succ := by simp,  
  have h2 : (list.cons (v.nth 0) (list.of_fn (λ (i : fin n), v.nth (i.succ)))).length = n.succ,
  simp,
  apply list.ext' h1 h2,
  intros i,
  by_cases hi : i = 0,
  { subst hi, 
    suffices : v.to_list.nth_le 0 _ = v.head,
      simpa,
    rcases v with ⟨_ | ⟨v_val_hd, _⟩⟩,
    { suffices : 0 = n.succ,
        cases this,
      rw ←h1, simp },
    { simp, refl } },
  { -- i ≠ 0
    have hj : ∃ j : fin n, i = j.succ,
    { have hi3 : i.val - 1 < n,
        have hi2 : i.val < n.succ := i.is_lt, 
        have hi' : i.val ≠ 0,
          cases i, intro hp, apply hi, ext, rw hp, refl,
        generalize hk : i.val = k,
        rw hk at hi2 hi',
        omega,
      use ⟨_, hi3⟩,
      cases i with i hin,
      simp,
      ext,
      simp,
      have hi4 : i ≠ 0,
        rintro rfl,apply hi,refl,
      rw nat.succ_eq_add_one,
      have hi5 : 0 < i,
        exact nat.pos_of_ne_zero hi4,
      apply (nat.sub_add_cancel _).symm,
      linarith },
    rcases hj with ⟨⟨j,hj⟩, rfl⟩,
    suffices : v.to_list.nth_le j.succ (h1.symm ▸ _) = v.nth (⟨j, hj⟩ : fin n).succ,
      simpa,
    rcases v with ⟨_ | ⟨hd,tl⟩⟩,
    { cases h1 },
    simp [vector.nth] },
end

lemma vector.to_list.succ' (n : ℕ) (M : Type) (v : vector M n.succ) :
v.to_list = list.of_fn
  (λ (i : fin n), v.nth i.cast_succ : fin n → M) ++ [v.nth ⟨n, nat.lt_succ_self _⟩] :=
begin
  have ht1 : v.to_list.length = n.succ := by simp,
  apply list.ext' ht1,
  { rintro ⟨i, hi⟩,
    by_cases h : i < n,
    { rw list.nth_le_append,
      { simp,
        suffices : v.to_list.nth_le i _ = v.nth ⟨i, hi⟩,
          convert this,
          convert h,
          simp,
        cases v with L hL,
        refl,
      } },
    have hin : i = n,
      rw nat.succ_eq_add_one at hi,
      linarith,
    subst hin,
    rw list.nth_le_append_right,
    simp,
    cases v, refl, simp },
  { simp }
end

section list

variables {G : Type} [mygroup.group G]

def list.prod' : list G → G
| [] := 1
| (h :: tl) := h * list.prod' tl 

@[simp] lemma list.prod_nil' : list.prod' ([] : list G) = 1 := rfl

@[simp] lemma list.prod_cons' (h : G) (tl : list G) :
  list.prod' (h :: tl) = h * list.prod' tl := rfl

lemma list.prod_append' (a b : list G) : (a ++ b).prod' = a.prod' * b.prod' :=
begin
  induction a with d hd I,
  { simp },
  { simp [*, mygroup.group.mul_assoc] },
end

lemma list.prod_singleton' (g : G) : [g].prod' = g :=
begin
  exact mygroup.group.mul_one g,
end

lemma list.prod_repeat' (d : ℕ) (g : G) : (list.repeat g d).prod' = ⦃d⦄^g :=
begin
  induction d with e he,
  { refl },
  simp [list.prod'],
  rw he,
  rw add_comm,
  rw mygroup.group.pow_add,
  rw mygroup.group.one_pow,
end

end list

namespace mygroup

variables {G : Type} [group G]

/-! ## The Predicate -/
/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def finmap.prod_eq_one {n : ℕ} : set (fin n → G) :=
λ f, (vector.of_fn f).to_list.prod' = 1

lemma mem_finmap_prod_eq_one {n : ℕ} (v : fin n → G) :
  v ∈ (finmap.prod_eq_one : set (fin n → G)) ↔ (vector.of_fn v).to_list.prod' = 1 :=
iff.rfl

variables {n : ℕ}

def fin.S.succ {n : ℕ} : fin n.succ ≃ fin n.succ :=
calc
fin n.succ ≃ zmod n.succ : fin.equiv_zmod
...         ≃ zmod n.succ : zmod.S
...         ≃ fin n.succ : fin.equiv_zmod.symm

def fin.S.succ' (n : ℕ) := @fin.S.succ n

-- I never use the next two things.
def fin.S.zero : fin 0 ≃ fin 0 := equiv.refl _

def fin.S (n : ℕ) : fin n ≃ fin n := nat.rec_on n fin.S.zero (λ d IH,
  fin.S.succ)

/-- the twist by fin.S.succ preserves the property that prod eq one -/
theorem finmap.prod_eq_one_succ {f : fin n.succ → G} :
finmap.prod_eq_one f → finmap.prod_eq_one (f ∘ fin.S.succ) :=
begin
  intro h,
  set p := (vector.of_fn f).to_list.prod' with hp,
  unfold finmap.prod_eq_one at *,
  -- want to break the goal into a product over fin n and last,
  -- and to break h into a product over head and tail
  -- want to break the goal into prod of either head and tail or of first and rest
  change (vector.of_fn (f ∘ (fin.S.succ' n))).to_list.prod' = 1,
  change (vector.of_fn (λ x, (f ∘ (fin.S.succ' n)) x)).to_list.prod' = 1,
  change (vector.of_fn (λ x, (f ((fin.S.succ' n) x)))).to_list.prod' = 1,
  rw vector.to_list.succ',
  rw list.prod_append',
  rw vector.to_list.succ at h,
  rw list.prod_cons' at h,
  apply (show ∀ a b : G, a * b = 1 → b * a = 1, begin
    intros a b hab,
    replace hab := mygroup.group.eq_inv_of_mul_eq_one hab,
    rw hab, simp,
  end),
  convert h,
  { simp, 
    congr',
    unfold fin.S.succ' fin.S.succ,
    simp,
    unfold zmod.S,
    simp,
    symmetry,
    rw equiv.eq_symm_apply,
    suffices : (0 : zmod n.succ) = fin.equiv_zmod ⟨n, (nat.lt_succ_self n)⟩ + 1,
      convert this,
    have h1 : (0 : zmod n.succ) = n + 1 := by simp,
    convert h1,
    ext, 
    convert eq.refl n,
    clear h hp p f h1,
    change zmod.val ((n : ℕ) : zmod n.succ) = n,
    erw zmod.val_cast_of_lt,
    exact nat.lt_succ_self n
  },
  unfold fin.S.succ' fin.S.succ,
  ext i,
  simp,
  congr',
  cases i with i hi,
  unfold zmod.S,
  symmetry,
  rw equiv.eq_symm_apply,
  simp,
  apply fin.eq_of_veq,
  unfold fin.equiv_zmod,
  change i.succ = _,
  simp,
  have : i.succ = ((i + 1 : ℕ) : zmod (n + 1)).val,
    rw zmod.val_cast_of_lt, apply nat.succ_lt_succ hi,
  convert this,
  simp,
  apply fin.eq_of_veq,
  exact (zmod.val_cast_of_lt (nat.lt_succ_of_lt hi)).symm,
end

lemma finmap.prod_eq_one_iterate {f : fin n.succ → G} (d : ℕ) :
finmap.prod_eq_one f → finmap.prod_eq_one (λ i, f ((⦃(d : ℤ)⦄^(fin.S.succ : fin n.succ ≃ fin n.succ) : fin n.succ ≃ fin n.succ).to_fun i)) :=
begin
  intro h,
  induction d with e he,
  { convert h },
  convert finmap.prod_eq_one_succ he,
  ext i,
  simp,
  congr' 1,
  rw group.pow_add,
  rw group.one_pow,
  refl
end

--instance foo : group (zmod n ≃ zmod n) := by apply_instance

lemma zmod.S.pow_k (k : ℕ) (n : ℕ) (d : zmod n) :
  (⦃k⦄^(zmod.S : zmod n ≃ zmod n)) d = k + d :=
begin
  induction k with e he,
  { simp },
  rw [nat.succ_eq_add_one, add_comm, int.coe_nat_add],
  rw group.pow_add,
  simp [he],
  simp [zmod.S],
  abel
end

lemma fin.S.succ.pow_k (k : ℕ) (n : ℕ) (d : fin n.succ) :
  (⦃k⦄^(fin.S.succ' n : fin n.succ ≃ fin n.succ)) d = k + d :=
begin
  -- evil proof
  apply zmod.S.pow_k k n.succ 
end

lemma zmod.S.pow_n (n : ℕ) (d : zmod n) :
  (⦃n⦄^(zmod.S : zmod n ≃ zmod n)) d = d :=
begin
  rw zmod.S.pow_k,
  simp,
end

lemma fin.S.succ.pow_n (n : ℕ) (d : fin n.succ) :
  (⦃((n.succ : ℕ) : ℤ)⦄^(fin.S.succ' n)) d = d := zmod.S.pow_n n.succ d

end mygroup
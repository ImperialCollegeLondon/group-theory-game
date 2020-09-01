import hom.theorems

namespace mygroup

open_locale classical

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

variables {G H : Type} [group G] [group H] {f : G →* H} 

def C_infty := ℤ

instance : has_le C_infty := { le := ((≤) : ℤ → ℤ → Prop) }

instance : group C_infty := 
{ mul := ((+) : ℤ → ℤ → ℤ), one := (0 : ℤ), inv := λ x, (- x : ℤ),
  mul_assoc := show ∀ x y z : ℤ, x + y + z = x + (y + z), by exact add_assoc,
  one_mul := show ∀ x, (0 : ℤ) + x = x, by exact zero_add,
  mul_left_inv := show ∀ x : ℤ, - x + x = 0, by exact neg_add_self }

instance : comm_group C_infty := 
{ mul_comm := show ∀ x y : ℤ, x + y = y + x, by exact add_comm
  .. show group C_infty, by apply_instance }

lemma C_infty_mul_comm (x y : C_infty) : x * y = y * x := 
  comm_group.mul_comm x y

lemma C_infty_generator :
  closure ({(1 : ℤ)} : set C_infty) = ⊤ :=
begin
  rw eq_top_iff,
  intros x h37,
  clear h37,
  show x ∈ (closure (({1} : set ℤ)) : subgroup C_infty),
  rw mem_closure_iff,
  intros H hH,
  rw singleton_subset_iff at hH,
  convert @pow_mem _ _ H 1 x hH,
  unfold group.pow,
  apply int.induction_on x,
  { refl },
  { intros i hi,
    rw group.iterate_succ,
    rw ←hi,
    exact add_comm (i : ℤ) 1,
  },
  { intros i hi,
    rw sub_eq_add_neg,
    rw add_comm,
    rw ←int.iterate.comp,
    rw ←hi,
    rw int.iterate.neg_one,
    refl }
end


def order_map (g : G) : C_infty →* G := 
{ to_fun := λ n, ⦃n⦄^g,
  map_mul' := λ x y, by rw ← group.pow_add; refl }

noncomputable def order (g : G) := let ker := kernel (order_map g) in 
  if h : ∃ o ∈ ker, ∀ k ∈ ker, o ≤ k then classical.some h else (0 : ℤ)

@[simp] lemma order_def (g : G) : order g =  
  if h : ∃ o ∈ kernel (order_map g), ∀ k ∈ kernel (order_map g), o ≤ k 
  then classical.some h else (0 : ℤ) := rfl

def mod (k : ℤ) : normal C_infty := 
{ carrier := { m : ℤ | k ∣ m },
  one_mem' := dvd_zero k,
  mul_mem' := λ _ _ hx hy, dvd_add hx hy,
  inv_mem' := λ x hx, (dvd_neg k x).2 hx,
  conj_mem' := λ x hx n,
    by { change k ∣ x at hx, change k ∣ n + x - n, simp [hx] } }

def cyclic (k : ℤ) := C_infty /ₘ mod k

namespace cyclic

instance cyclic.group (k : ℤ) : group (cyclic k) := 
  by unfold cyclic; apply_instance

instance cyclic.comm_group (k : ℤ) : comm_group (cyclic k) := 
{ mul_comm := 
    begin
      intros x y,
      rcases exists_mk x with ⟨x, rfl⟩,
      rcases exists_mk y with ⟨y, rfl⟩,
      rw [coe_mul, C_infty_mul_comm, ← coe_mul]
    end,
  .. show group (cyclic k), by apply_instance }

def generator {n : ℕ} : cyclic n := quotient.mk _ (1 : ℤ)

--#check closure_image
--#check map_closure

variable (n : ℕ)

local notation `q` := quotient.mk (mod n)

lemma generator_generates (n : ℕ) :
  closure ({cyclic.generator} : set (cyclic n)) = ⊤ :=
begin
  rw eq_top_iff,
  rintro x h37, clear h37,
  suffices : x ∈ map q (closure {(1 : ℤ)}),
    rw ←closure_singleton at this,
    exact this,
  rw C_infty_generator,
  tidy,
end

def nat.coe : ℕ → C_infty := λ i, (i : ℤ)

def nat.coe' : (ℕ ↪ C_infty) :=
{ to_fun := λ i, (i : ℤ),
  inj' := λ a b, int.of_nat.inj }

@[reducible] noncomputable def inv_fun_aux (x : cyclic n) :=
(classical.indefinite_description _ (exists_mk x))

lemma useful (a b : ℤ) (ha1 : 0 ≤ a) (ha2 : a < n) (hb1 : 0 ≤ b)
  (hb2 : b < n) (h : (n : ℤ) ∣ (a - b)) : a = b :=
begin
  cases h with d hd,
  have h : d = 0 ∨ d ≤ -1 ∨ 1 ≤ d,
    rcases lt_trichotomy d 0 with _ | _ | _,
      right, left, linarith,
      left, exact h,
      right, right, linarith,
  rcases h with rfl | h | h,
  { simpa [sub_eq_zero] using hd },
  { have hd2 : a - b ≤ -n,
      rw hd,
      convert int.mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ n, by linarith),
      ring,
    exfalso,
    linarith },
  { have hd2 : (n : ℤ) ≤ a - b,
      rw hd,
      convert int.mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ n, by linarith),
      ring,
    exfalso,
    linarith },
end

--set_option pp.proofs true
noncomputable def fin.equiv (hn : 0 < n) : fin n ≃ cyclic n :=
{ to_fun := λ i, q (i.val : ℤ),
  inv_fun := λ x, ⟨int.nat_abs ((inv_fun_aux n x).val % (n : ℤ)),
    begin
      have h3 : (n : ℤ) ≠ 0,
      { linarith },
      have h2 := int.mod_nonneg _ h3,
      convert @int.nat_abs_lt_nat_abs_of_nonneg_of_lt _ n h2 _,
      convert int.mod_lt _ h3,
      simp
    end⟩,
  left_inv := begin
    rintro ⟨x, hx⟩,
    tidy,
    have h : (x : ℤ).nat_abs = x := int.nat_abs_of_nat x,
    convert h,
    suffices : ((inv_fun_aux n (⇑(mk (mod ↑n)) (x : ℤ))).val % ↑n : ℤ) = x,
    exact this,
    have h2 := (inv_fun_aux n (q (x : ℤ))).2,
    change q _ = q _ at h2,
    generalize h3 : (inv_fun_aux n (⇑(mk (mod ↑n)) (x : ℤ))).val = z,
    rw h3 at h2,
    replace h2 := mem_kernel_of_eq h2,
    rw kernel_mk at h2,
    cases h2 with d hd,
    change (-(x : ℤ)) + (z : ℤ) = _ at hd,
    have hn2 : (n : ℤ) ≠ 0 := by linarith,
    apply useful n,
    { refine int.mod_nonneg _ hn2 },
    { convert int.mod_lt _ hn2, simp },
    { linarith },
    { norm_num, exact hx },
    { rw neg_add_eq_iff_eq_add at hd,
      rw hd,
      use 0,
      rw mul_zero,
      rw sub_eq_zero,
      suffices : (x : ℤ) % n = x,
        simpa,
      apply int.mod_eq_of_lt, linarith, norm_num, assumption },
  end,
  right_inv := begin
    intro x,
    have h : q _ = x := (inv_fun_aux n x).2,
    simp,
    convert h using 1,
    apply mk_eq'.2,
    clear h,
    let z : ℤ := (inv_fun_aux n x).val,
    change -z + int.nat_abs (z % n) ∈ _,
    have h := int.mod_add_div z n,
    conv_lhs begin
      congr,rw ←h,
    end,
    have h2 : 0 ≤ z % n := int.mod_nonneg _ (by linarith : (n : ℤ) ≠ (0 : ℤ) ),
    use -(z / ↑n),
    rw ←int.eq_nat_abs_of_zero_le h2,
    ring
  end,
} 

lemma fincard_cyclic (hn : 0 < n) : fincard' (cyclic n) = n :=
begin
  rw ←fincard.of_equiv (fin.equiv n hn),
  rw ← fincard.card_eq_fincard,
  exact fintype.card_fin n,
end

-- noncomputable instance (hn : 0 < n) : fintype (cyclic n) :=
-- { elems := finset.map (fin.coe n) $ finset.range n,
--   complete := begin
        
--   end
-- }

end cyclic

end mygroup
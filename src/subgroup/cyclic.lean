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
  rw _root_.eq_top_iff,
  intros x _,
  change _ ∈ (closure ({1} : set ℤ) : subgroup C_infty),
  rw mem_closure_iff,
  intros H hH,
  rw singleton_subset_iff at hH,
  convert @pow_mem _ _ H 1 x hH,
  unfold group.pow,
  apply int.induction_on x,
    { refl },
    { intros i hi,
      rw [group.iterate_succ, ←hi],
      exact add_comm (i : ℤ) 1 },
    { intros i hi,
      rw [sub_eq_add_neg, add_comm, ← int.iterate.comp, 
          ← hi, int.iterate.neg_one],
      refl }
end

def order_map (g : G) : C_infty →* G := 
{ to_fun := λ n, ⦃n⦄^g,
  map_mul' := λ x y, by rw ← group.pow_add; refl }

@[simp] lemma order_map_def (g : G) (k : ℤ) : order_map g k = ⦃k⦄^g := rfl

-- noncomputable def order (g : G) : ℤ := let ker := kernel (order_map g) in 
--   if h : ∃ (o ∈ ker) (H : 0 < o), ∀ k ∈ ker, 0 < k → o ≤ k then classical.some h 
--   else (0 : ℤ)

-- @[simp] lemma order_def (g : G) : order g =  
--   if h : ∃ o ∈ kernel (order_map g), ∀ k ∈ kernel (order_map g), o ≤ k 
--   then classical.some h else (0 : ℤ) := rfl

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
      linarith },
    { have hd2 : (n : ℤ) ≤ a - b,
        rw hd,
        convert int.mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ n, by linarith),
        ring,
      linarith },
end

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
    convert (int.nat_abs_of_nat x),
    suffices : ((inv_fun_aux n ((mk (mod ↑n)) (x : ℤ))).val % n : ℤ) = x,
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
        rw hd, use 0, rw [mul_zero, sub_eq_zero],
        suffices : (x : ℤ) % n = x,
          simpa,
        apply int.mod_eq_of_lt, linarith, norm_num, assumption }
  end,
  right_inv := begin
    intro x,
    have h : q _ = x := (inv_fun_aux n x).2,
      simp,
    convert h using 1,
    apply mk_eq'.2,
    let z : ℤ := (inv_fun_aux n x).val,
    change -z + int.nat_abs (z % n) ∈ _,
    have h := int.mod_add_div z n,
    conv_lhs begin congr, rw ←h, end,
    use -(z / ↑n), 
    rw ←int.eq_nat_abs_of_zero_le 
      (int.mod_nonneg _ (by linarith : (n : ℤ) ≠ (0 : ℤ) )), 
    ring
  end } 

lemma fincard_cyclic (hn : 0 < n) : fincard' (cyclic n) = n :=
begin
  rw [←fincard.of_equiv (fin.equiv n hn), ← fincard.card_eq_fincard],
  exact fintype.card_fin n,
end

noncomputable instance (n : ℕ) : fintype (cyclic ↑(n.succ)) :=
begin
  exact @fintype.of_equiv _ _ _ (mygroup.cyclic.fin.equiv n.succ (nat.zero_lt_succ n)),
end

def closure_singleton (g : G) : subgroup G := 
{ carrier := { c | ∃ k : ℤ, c = ⦃k⦄^g },
  one_mem' := ⟨0, group.zero_pow g⟩,
  mul_mem' := 
    begin
      rintro _ _ ⟨k, rfl⟩ ⟨l, rfl⟩,
      exact ⟨k + l, (group.pow_add _ _ _).symm⟩
    end,
  inv_mem' := 
    begin
      rintro _ ⟨k, rfl⟩, refine ⟨-k, _⟩,
      rw [← group.pow_neg_one_inv, ← group.pow_mul], simp,
    end }

lemma mem_closure_singleton_iff {g x : G} : 
  x ∈ closure_singleton g ↔ ∃ k : ℤ, x = ⦃k⦄^g := iff.rfl

lemma closure_singleton_eq (g : G) : 
  closure ({g} : set G) = closure_singleton g :=
begin
  apply le_antisymm,
    { rw closure_le, intros x hx,
      rw mem_singleton_iff.1 hx,
      exact ⟨1, (group.one_pow _).symm⟩ },
    { rintros _ ⟨k, rfl⟩, 
      change _ ∈ closure ({g} : set G),
      rw mem_closure_iff, intros H hg,
      rw singleton_subset_iff at hg,
      exact pow_mem _ hg }
end

lemma pow_eq_mul (k m : C_infty) : ⦃(m : ℤ)⦄^k = ((k : ℤ) * m : ℤ) := 
begin
  apply int.induction_on m,
    { simpa },
    { intros i hi,
      rw [group.pow_add, hi, group.one_pow, mul_add, mul_one], refl },
    { intros i hi, 
      rw [sub_eq_add_neg, group.pow_add, hi, group.pow_neg_one_inv, mul_add, 
          mul_neg_one], refl }
end

lemma mod_eq_closure (k : ℤ) : (mod k).to_subgroup = closure {k} :=
begin
  rw closure_singleton_eq,
  ext, split; rintro ⟨m, rfl⟩,
    { exact ⟨m, (pow_eq_mul _ _).symm⟩ },
    { rw pow_eq_mul, refine ⟨m, rfl⟩ }
end

end cyclic

-- lemma group.pow_order (g : G) : ⦃(order g)⦄^g = 1 := 
-- begin
--   unfold order,
--   dsimp,
--   split_ifs,
--     { rw [← order_map_def, ← mem_kernel],
--       cases classical.some_spec h, assumption },
--     { exact group.zero_pow _ }
-- end

namespace cyclic

-- noncomputable def closure_singleton_to_cyclic (g : G) : 
--   closure_singleton g → cyclic (order g) :=
-- λ g', mk (mod (order g)) $ classical.some (mem_closure_singleton_iff.1 g'.2)

-- noncomputable def fin_to_closure_singleton (g : G) : 
--   fin (int.nat_abs (order g)) → closure_singleton g :=
-- λ n, ⟨⦃n⦄^g, ⟨n, rfl⟩⟩

-- lemma bijective_cyclic_to_closure_singleton {g : G} : 
--   function.bijective (fin_to_closure_singleton g) :=
-- begin
--   split,
--     { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy,
--       simp [fin_to_closure_singleton] at hxy,
--       rw fin.mk.inj_iff,
--       by_contra h,
--       cases lt_or_le x y,
--       suffices : ⦃y - x⦄^g = 1,
--         sorry,
--       sorry,
--       sorry
--     },
--     { sorry },
-- end

-- noncomputable def cyclic_iso_closure_singleton (g : G) : 
--   cyclic (order g) ≅ closure_singleton g :=
-- { to_fun := _,
--   map_mul' := _,
--   is_bijective := _ }

end cyclic

end mygroup
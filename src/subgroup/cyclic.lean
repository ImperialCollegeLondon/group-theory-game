import hom.isomorphism
import orbit.basic

namespace mygroup

open_locale classical

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

variables {G H : Type} [group G] [group H] {f : G →* H} 

def C_infty := ℤ

instance cyclic.to_int : has_coe C_infty ℤ := ⟨id⟩
instance int.to_C_infty : has_coe ℤ C_infty := ⟨id⟩
instance C_infty_infinite : infinite C_infty := 
  by change infinite ℤ; apply_instance

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
  rw group.pow_def,
  apply int.induction_on x,
    { refl },
    { intros i hi,
      rw [group.iterate_succ, ← hi],
      exact add_comm (i : ℤ) 1 },
    { intros i hi,
      rw [sub_eq_add_neg, add_comm, ← int.iterate.comp, 
          ← hi, int.iterate.neg_one], refl }
end

def order_map (g : G) : C_infty →* G := 
{ to_fun := λ n : ℤ, g ^ n,
  map_mul' := λ x y, by rw ← group.pow_add; refl }

@[simp] lemma order_map_def (g : G) (k : ℤ) : order_map g k = g ^ k := rfl

noncomputable def order (g : G) := 
  let s := (coe : ℕ → ℤ) ⁻¹' ((kernel $ order_map g) : set C_infty) in 
  if h : ∃ o ∈ s, 0 < o then nat.find h else 0

lemma order_def (g : G) : order g =
  if h : ∃ o ∈ (coe : ℕ → ℤ) ⁻¹' ((kernel $ order_map g) : set C_infty), 0 < o 
  then nat.find h else 0 := rfl

@[simp] lemma pow_order_eq_one (g : G) : g ^ (order g : ℤ) = 1 :=
begin
  by_cases ∃ o ∈ (coe : ℕ → ℤ) ⁻¹' ((kernel $ order_map g) : set C_infty), 0 < o,
    { rcases nat.find_spec h with ⟨_, _⟩,
      rwa [order_def, dif_pos h, ← order_map_def, ← mem_kernel] },
    { rw [order_def, dif_neg h], simp }
end 

lemma mem_order_map_kernel_coe {n : ℕ} {a : G} : 
  n ∈ (coe : ℕ → ℤ) ⁻¹' (((order_map a).kernel) : set C_infty) ↔ a ^ (n : ℤ) = 1 := 
iff.rfl

lemma of_order_eq_zero {g : G} (h : order g = 0) : 
  ¬ ∃ o ∈ (coe : ℕ → ℤ) ⁻¹' ((kernel $ order_map g) : set C_infty), 0 < o :=
begin
  intro ho,
  rw [order_def, dif_pos ho] at h, 
  rcases nat.find_spec ho with ⟨_, _⟩,
  linarith
end

lemma order_eq_zero_iff (g : G) : order g = 0 ↔ ∀ n, 0 < n → g ^ (n : ℤ) ≠ 1 := 
begin
  split; intro h,
    { intros n hn hgn,
      refine of_order_eq_zero h ⟨int.nat_abs n, _, _⟩,
      change _ ∈ kernel (order_map g),
      rwa [← int.abs_eq_nat_abs, abs_of_pos hn],
      rw (show 0 = int.nat_abs 0, by simp),
      exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt (le_refl _) hn },
    { rw [order_def, dif_neg], push_neg,
      intro o, by_contra ho, push_neg at ho,
      exact h o (by simp [ho.2]) (mem_order_map_kernel_coe.1 ho.1) }
end

lemma order_le_of_pow_order_eq_one {g : G} {k : ℕ} 
  (hk : 0 < k) (hg : g ^ (k : ℤ) = 1) : order g ≤ k :=
begin
  by_cases ∃ o ∈ (coe : ℕ → ℤ) ⁻¹' ((kernel $ order_map g) : set C_infty), 0 < o,
    { rw [order_def, dif_pos h], by_contra hn,
      refine nat.find_min _ (not_le.1 hn) ⟨_, hk⟩,
      exact mem_order_map_kernel_coe.2 hg },
    { rw [order_def, dif_neg h], exact zero_le _ }
end

lemma pow_injective_of_lt_order_of {n m : ℕ} (a : G) (hn : n < order a) 
  (hm : m < order a) (eq : a ^ (n : ℤ) = a ^ (m : ℤ)) : n = m := 
begin
  wlog h : n ≤ m, by_contra hneq,
  replace hneq := lt_of_le_of_ne h hneq,
  rw [← group.mul_right_cancel_iff (a ^ (-n : ℤ)), ← group.pow_add,
      ← group.pow_add, add_neg_self, group.pow_zero, ← int.sub_eq_add_neg,
      ← int.coe_nat_sub (le_of_lt hneq)] at eq,
  exact not_lt.2 (order_le_of_pow_order_eq_one (by omega) eq.symm) (by omega),
end

lemma pow_eq_mod_order_of {n : ℕ} {a : G} : a ^ (n : ℤ) = a ^ ((n % order a) : ℤ) := 
calc a ^ (n : ℤ) = a ^ ((n % order a + order a * (n / order a)) : ℤ) : 
by conv_lhs { rw [← nat.mod_add_div n (order a)] }; congr
  ... = a ^ (n % order a : ℤ) :
by rw [group.pow_add, mul_comm, group.pow_mul, pow_order_eq_one, group.one_pow, group.mul_one]

lemma order_of_dvd_of_pow_eq_one {n : ℕ} {a : G} (h : a ^ (n : ℤ) = 1) : order a ∣ n :=
begin
   by_cases hzero : n = 0, 
    { rw hzero, exact dvd_zero _ }, 
    { replace hzero : 0 < n := nat.pos_of_ne_zero hzero,
      rw order_def, split_ifs with ho,
        { by_contra hndvd,
          have : n % order a < order a,
            { refine nat.mod_lt _ _,
              by_contra hnzero, push_neg at hnzero,
              rw le_zero_iff_eq at hnzero,
              exact of_order_eq_zero hnzero ⟨n, mem_order_map_kernel_coe.1 h, hzero⟩ }, 
          rw [order_def, dif_pos ho] at this,
          refine nat.find_min ho this ⟨_, _⟩,
          rw [mem_order_map_kernel_coe, ← h],
          convert pow_eq_mod_order_of.symm,
          rw [order_def, dif_pos ho], exact int.nat_abs_of_nat _,
          exact nat.pos_of_ne_zero (mt nat.dvd_of_mod_eq_zero hndvd) },
        { have : order a = 0, rw [order_def, dif_neg ho],
          rw order_eq_zero_iff at this,
          exfalso, refine this n _ h, linarith } }
end

def mod (k : ℤ) : normal C_infty := 
{ carrier := { m : ℤ | k ∣ m },
  one_mem' := dvd_zero k,
  mul_mem' := λ _ _ hx hy, dvd_add hx hy,
  inv_mem' := λ x hx, (dvd_neg k x).2 hx,
  conj_mem' := λ x hx n,
    by { change k ∣ x at hx, change k ∣ n + x - n, simp [hx] } }

def cyclic (k : ℤ) := C_infty /ₘ mod k

instance cyclic.group (k : ℤ) : group (cyclic k) := 
  by unfold cyclic; apply_instance

instance cyclic.comm_group (k : ℤ) : comm_group (cyclic k) := 
{ mul_comm := 
    begin
      intros x y,
      rcases exists_mk x with ⟨x, rfl⟩,
      rcases exists_mk y with ⟨y, rfl⟩,
      rw [quotient.coe_mul, C_infty_mul_comm, ← quotient.coe_mul]
    end,
  .. show group (cyclic k), by apply_instance }

namespace cyclic

def C_infty_iso_cyclic_zero : C_infty ≅ cyclic 0 := 
{ is_bijective := 
  begin
    split,
      { intros x y hxy,
        change (x : C_infty /ₘ mod 0) = y at hxy,
        rw mk_eq' at hxy,
        change (0 : ℤ) ∣ (-y : ℤ) + x at hxy,
        rwa [zero_dvd_iff, add_comm, add_neg_eq_zero] at hxy },
      { intro y,
        rcases exists_mk y with ⟨x, rfl⟩,
        exact ⟨x, rfl⟩ }
  end, .. quotient.mk _ }

def generator {n : ℕ} : cyclic n := quotient.mk _ (1 : ℤ)

variable (n : ℕ)
local notation `q` := quotient.mk (mod n)

lemma generator_generates (n : ℕ) :
  closure ({ generator } : set (cyclic n)) = ⊤ :=
begin
  rw eq_top_iff, rintro x _,
  suffices : x ∈ map q (closure {(1 : ℤ)}),
    rw ← closure_singleton at this,
    exact this,
  rw C_infty_generator, tidy
end

def nat.coe : ℕ → C_infty := λ i, (i : ℤ)

def nat.coe' : ℕ ↪ C_infty :=
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
    conv_lhs begin congr, rw ← h, end,
    use -(z / ↑n), 
    rw ←int.eq_nat_abs_of_zero_le 
      (int.mod_nonneg _ (by linarith : (n : ℤ) ≠ (0 : ℤ) )), 
    ring
  end } 

lemma fincard_cyclic : fincard (cyclic n) = n :=
begin
  by_cases hn : 0 < n,
    { rw [← fincard.of_equiv (fin.equiv n hn), ← fincard.card_eq_fincard],
      exact fintype.card_fin n },
    { push_neg at hn, rw nat.le_zero_iff at hn, rw hn,
      unfold fincard, unfold finset.univ',
      rw dif_neg,
        { exact finset.card_empty },
        { rw not_nonempty_fintype,
          apply infinite.of_surjective 
            (inv_fun C_infty_iso_cyclic_zero.to_fun) (inv_fun_surjective _),
          exact C_infty_iso_cyclic_zero.is_bijective.1 } }
end

noncomputable instance (n : ℕ) : fintype (cyclic ↑(n.succ)) :=
  @fintype.of_equiv _ _ _ (mygroup.cyclic.fin.equiv n.succ (nat.zero_lt_succ n))

def closure_singleton (g : G) : subgroup G := 
{ carrier := { c | ∃ k : ℤ, c = g ^ k },
  one_mem' := ⟨0, group.pow_zero g⟩,
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
  x ∈ closure_singleton g ↔ ∃ k : ℤ, x = g ^ k := iff.rfl

lemma closure_singleton_eq (g : G) : 
  closure ({g} : set G) = closure_singleton g :=
begin
  apply le_antisymm,
    { rw closure_le, intros x hx,
      rw mem_singleton_iff.1 hx,
      exact ⟨1, (group.pow_one _).symm⟩ },
    { rintros _ ⟨k, rfl⟩, 
      change _ ∈ closure ({g} : set G),
      rw mem_closure_iff, intros H hg,
      rw singleton_subset_iff at hg,
      exact pow_mem _ hg }
end

lemma pow_eq_mul (k : C_infty) (m : ℤ): 
  k ^ m = (k * m : ℤ) := 
begin
  apply int.induction_on m,
    { simpa },
    { intros i hi,
      rw [group.pow_add, hi, group.pow_one, mul_add, mul_one], refl },
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

def to_hom (g : G) (n : ℕ) (h : g ^ (n : ℤ) = 1) : cyclic n →* G :=
  quotient.lift (order_map g) _
begin
  rw [cyclic.mod_eq_closure, subgroup.closure_le],
  show _ ⊆ _, rw set.singleton_subset_iff, exact h,
end

end cyclic

end mygroup
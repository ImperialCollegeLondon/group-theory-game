import subgroup.cyclic

namespace mygroup

open_locale classical

open mygroup mygroup.subgroup mygroup.quotient group_hom function set

namespace torsion

def torsion_set (G : Type) [comm_group G] := { g : G | order g ≠ 0 }

variables {G : Type} [comm_group G]

lemma torsion_set_def : torsion_set G = { g : G | order g ≠ 0 } := rfl
lemma mem_torsion_set_iff (g : G) : g ∈ torsion_set G ↔ order g ≠ 0 := iff.rfl

attribute [simp] mem_torsion_set_iff

lemma one_mem_torsion_set : (1 : G) ∈ torsion_set G :=
by rw [mem_torsion_set_iff, order_one_eq_one]; exact one_ne_zero

/-- Two elements of an abelian group with finite order multiplied is also an 
  element of finite order -/
lemma ne_zero_order_mul_ne_zero {g h : G} 
  (hg : order g ≠ 0) (hh : order h ≠ 0) : order (g * h) ≠ 0 :=
begin
  intro heq,
  rw order_eq_zero_iff at heq,
  rw ← zero_lt_iff_ne_zero at hg hh,
  apply heq (order g * order h), 
    { apply mul_pos; simpa only [int.coe_nat_pos] },
    { rw [← group.mul_pow, mul_comm, group.pow_mul, pow_order_eq_one, 
          group.one_pow, mul_comm, group.pow_mul, pow_order_eq_one, 
          group.one_pow, group.mul_one] }
end

lemma mul_mem_torsion_set {g h : G} 
  (hg : g ∈ torsion_set G) (hh : h ∈ torsion_set G) : g * h ∈ torsion_set G :=
ne_zero_order_mul_ne_zero hg hh

lemma inv_mem_torsion_set {g : G} (hg : g ∈ torsion_set G) : 
  g⁻¹ ∈ torsion_set G :=
begin
  intro h,
  apply hg,
  rw order_eq_zero_iff at h ⊢,
  intros n hn hgn,
  exact h n hn 
    (by rw [← group.pow_neg_one_inv, ← group.pow_mul, mul_comm, group.pow_mul, hgn]; simp),
end

/-- The torsion subgroup of an abelian group is the subgroup of all elements of 
  finite order -/
def torsion_subgroup (G : Type) [comm_group G] : subgroup G :=
{ carrier := torsion_set G,
  one_mem' := one_mem_torsion_set,
  mul_mem' := λ _ _, mul_mem_torsion_set,
  inv_mem' := λ _, inv_mem_torsion_set }

lemma mem_torsion_subgroup_iff (g : G) : g ∈ torsion_subgroup G ↔ order g ≠ 0 := iff.rfl

attribute [simp] mem_torsion_subgroup_iff

end torsion

def torsion (G : Type) [comm_group G] : normal G :=
  normal.of_comm_subgroup $ torsion.torsion_subgroup G

-- Temporary (should infer from the fact that the normal subgroups form a complete lattice)
instance {G : Type} [group G] : has_bot $ normal G := 
⟨ { conj_mem' := λ _ hn _,
      by rw [(mem_trivial_carrier_iff _).mp hn, group.mul_one, 
        group.mul_right_inv]; exact one_mem _, .. subgroup.trivial } ⟩

lemma normal.mem_bot_iff {G : Type} [group G] {x : G} : x ∈ (⊥ : normal G) ↔ x = 1 :=
begin 
  split, intro h,
    { rw [← mem_singleton_iff, ← bot_eq_singleton_one], 
      rw [bot_eq_trivial], exact h },
    { rintro rfl, exact one_mem _ }
end

namespace torsion

variables {G : Type} [comm_group G]

@[simp] lemma mem_torsion_iff (g : G) : g ∈ torsion G ↔ order g ≠ 0 := iff.rfl

/-- The quotient of an abelian group by its torsion subgroup is also an 
  abelian subgroup -/
instance : comm_group $ G /ₘ torsion G := 
  { mul_comm := λ a b,
      let ⟨g, hg⟩ := exists_mk a in
      let ⟨h, hh⟩ := exists_mk b in
      by rw [← hg, ← hh, quotient.coe_mul, group.mul_comm, ← quotient.coe_mul],
  .. show group (G /ₘ torsion G), by apply_instance } -- french quotes does not work

/-- The torsion of the quotient by the torsion is the trivial subgroup -/
lemma of_quotient_torsion_eq_bot : torsion (G /ₘ torsion G) = ⊥ :=
begin
  ext, rw [normal.mem_bot_iff], split,
    { intro h, 
      rcases exists_mk g with ⟨g, rfl⟩,
      rw [← coe_one, mk_eq', group.one_inv, group.one_mul],
      intro hg, apply h,
      rw order_eq_zero_iff at hg ⊢,
      intros n hn hgn,
      rw [coe_pow, ← coe_one, mk_eq', group.one_inv, 
        group.one_mul, mem_torsion_iff, ← zero_lt_iff_ne_zero] at hgn,
      refine hg (n * order (g ^ n)) (mul_pos hn $ int.coe_nat_pos.2 hgn) _,
      rw [mul_comm, group.pow_mul, pow_order_eq_one] },
    { rintro rfl, exact one_mem _ }
end

end torsion

end mygroup
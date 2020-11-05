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
def torsion (G : Type) [comm_group G] : subgroup G :=
{ carrier := torsion_set G,
  one_mem' := one_mem_torsion_set,
  mul_mem' := λ _ _, mul_mem_torsion_set,
  inv_mem' := λ _, inv_mem_torsion_set }

lemma mem_torsion_iff (g : G) : g ∈ torsion G ↔ order g ≠ 0 := iff.rfl

-- lemma torsion_torsion_eq_bot : G /ₘ torsion G 

end torsion

end mygroup
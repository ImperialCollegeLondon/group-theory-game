import subgroup.basic

/-
Let G be a group. The type of subgroups of G is `subgroup G`. 
In other words, if `H : subgroup G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min (and even sup and inf). 

We will prove this here.
-/

open_locale classical

namespace mygroup

open group set

variables {G : Type} [group G]
variables {H K : subgroup G}

namespace subgroup

-- The intersect of two subgroups is also a subgroup
def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' := ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩, 
  ⟨H.mul_mem hhx hhy, K.mul_mem hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
  ⟨H.inv_mem hhx, K.inv_mem hhy⟩}

lemma inf_def (H K : subgroup G) : (inf H K : set G) = (H : set G) ∩ K := rfl 

/- 
We will consider the closure of a set as the intersect of all subgroups
containing the set
-/
instance : has_Inf (subgroup G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem (by apply mem_bInter_iff.1 hx i h) }⟩

variable {ι : Type*}

-- The intersect of a set of subgroups is a subgroup
def infi (H : ι → subgroup G) : subgroup G := 
{ carrier := ⋂ i, H i,
  one_mem' := mem_Inter.mpr $ λ i, (H i).one_mem,
  mul_mem' := λ _ _ hx hy, mem_Inter.mpr $ λ i, 
  by {rw mem_Inter at *, from mul_mem (H i) (hx i) (hy i)},
  inv_mem' := λ x hx, mem_Inter.mpr $ λ i, (H i).inv_mem $ by apply mem_Inter.mp hx }

def closure (S : set G) : subgroup G := Inf {H | S ⊆ H}

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : subgroup G, S ⊆ H → x ∈ H := mem_bInter_iff

/- We will now prove some lemmas that are helpful in proving subgroups 
form a galois_insertion with the coercion to set-/

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : subgroup G) : closure S ≤ H ↔ S ≤ H :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y,
      unfold closure, unfold Inf, 
      rw mem_bInter_iff, intro hy,
      exact hy H h }
end

lemma closure_le' (S : set G) (H : subgroup G) : 
  (closure S : set G) ⊆ H ↔ S ⊆ H := closure_le S H

lemma closure_le'' (S : set G) (H : subgroup G) : 
  (∀ x, x ∈ closure S → x ∈ H) ↔ (∀ x, x ∈ S → x ∈ H) := closure_le S H

lemma closure_self {H : subgroup G} : closure (H : set G) = H :=
begin
  rw ←subgroup.ext'_iff, ext,
  split; intro hx,
    { apply subset.trans _ ((closure_le (H : set G) H).2 (subset.refl H)), 
      exact hx, exact subset.refl _
    },
    { apply subset.trans (le_closure (H : set G)), 
      intros g hg, assumption, assumption }
end

lemma closure_induction {p : G → Prop} {x} {k : set G} (h : x ∈ closure k)
  (Hk : ∀ x ∈ k, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 Hk h

/-
Now, by considering the coercion between subgroup G → set G, we cheat a bit
by transfering the partial order on set to the partial order on subgroups.

We do this because galois_insertion requires preorders and partial orders
extends preoders.
-/
instance : partial_order (subgroup G) := 
{.. partial_order.lift (coe : subgroup G → set G) (λ x y, subgroup.ext')}

/-
Finially we prove that subgroups form a galois_insertion with the coercion 
to set.
-/
def gi : @galois_insertion (set G) (subgroup G) _ _ closure (λ H, H.carrier) :=
{ choice := λ S _, closure S,
  gc := λ H K,
    begin
      split; intro h,
        { exact subset.trans (le_closure H) h },
        { exact (closure_le _ _).2 h },
    end,
  le_l_u := λ H, le_closure (H : set G),
  choice_eq := λ _ _, rfl }

/-
With that it follows that subgroups form a complete lattice!
-/
instance : complete_lattice (subgroup G) :=
{.. galois_insertion.lift_complete_lattice gi}

def trivial : subgroup G := 
  ⟨{(1 : G)}, set.mem_singleton 1, 
    λ _ _ hx hy, by rw set.mem_singleton_iff at *; simp [hx, hy],
    λ _ hx, by rw set.mem_singleton_iff at *; rw hx; exact group.one_inv⟩

lemma mem_trivial_iff (g : G) : g ∈ (trivial : subgroup G) ↔ g = 1 := iff.rfl

lemma mem_trivial_carrier_iff (g : G) : g ∈ (trivial : subgroup G).carrier ↔ g = 1 := iff.rfl

lemma bot_eq_trivial : (⊥ : subgroup G) = trivial :=
begin
  apply le_antisymm,
    { change closure (∅ : set G) ≤ _,
      rw closure_le, finish },
    { intros x hx,
      change x ∈ {(1 : G)} at hx, 
      rw set.mem_singleton_iff at hx,
      subst hx, unfold_coes, rw mem_coe,
      exact one_mem ⊥ }
end 

lemma bot_eq_singleton_one : ((⊥ : subgroup G) : set G) = {1} :=
by rw bot_eq_trivial; refl

lemma mem_bot_iff {x : G} : x ∈ (⊥ : subgroup G) ↔ x = 1 :=
begin 
  split; intro h,
    rw [← mem_singleton_iff, ← bot_eq_singleton_one], exact h,
    rw [bot_eq_trivial], exact h
end

lemma fincard_bot : fincard (⊥ : subgroup G) = 1 :=
by rw [← @fincard.card_singleton_eq_one _ (1 : G), ← bot_eq_singleton_one]; refl

lemma eq_top_iff' (H : subgroup G) : H = ⊤ ↔ ∀ g, g ∈ H :=
begin
  split,
  { rintro rfl,
    intro g,
    show g ∈ ((⊤ : subgroup G) : set G),
    rw ←singleton_subset_iff,
    show ({g} : set G) ≤ _,
    rw ←closure_le, simp },
  { intro h,
    rw eq_top_iff,
    intros g hg,
    apply h  }
end

-- scary example!
-- SL₂(ℝ) acts on the upper half plane {z : ℂ | Im(z) > 0}
-- (a b; c d) sends z to (az+b)/(cz+d)
-- check this is an action
-- so SL₂(ℤ) acts on the upper half plane
-- and H, the stabilizer of i ,is cyclic order 4
-- generated by (0 -1; 1 0)
-- and K, the stabilizer of e^{2 pi i/6}, is cyclic order 6
-- generated by something like (1 1; -1 0) maybe
-- Turns out that the smallest subgroup of SL₂(ℤ)
-- containing H and K is all of SL₂(ℤ)!
-- In particular if H and K are finite, but neither of
-- them are normal, then H ⊔ K can be huge

example (H K : subgroup G) : subgroup G := H ⊔ K

-- theorem: if K is normal in G then H ⊔ K is just 
-- literally {hk : h ∈ H, k ∈ K}

variables {H K}

open normal

/-- The supremum of two subgroups induced by the Galois insertion is the closure 
  of the union of their carriers -/
lemma sup_def : H ⊔ K = closure (H.carrier ⊔ K.carrier) := rfl

/-- The supremum of two subgroups is larger then their union -/
lemma mem_sup_of_mem {x} (hx : x ∈ H ∨ x ∈ K) : x ∈ H ⊔ K :=
begin
  rw sup_def,
  change x ∈ ⋂ (t : subgroup G) (H : H.carrier ∪ K.carrier ⊆ t), ↑t,
  refine mem_bInter (λ S hS, hS hx)
end

lemma mem_sup_of_mem_left {x} (hx : x ∈ H) : x ∈ H ⊔ K :=
by { apply mem_sup_of_mem, left, assumption }

lemma mem_sup_of_mem_right {x} (hx : x ∈ K) : x ∈ H ⊔ K :=
by { apply mem_sup_of_mem, right, assumption }

lemma mem_inf {H K : subgroup G} {g : G} : 
  g ∈ H ⊓ K ↔ g ∈ H ∧ g ∈ K := 
begin
  change g ∈ closure ((H : set G) ∩ K) ↔ _,
  rw [←inf_def H K, closure_self], refl
end

namespace product

/-- The product of a subgroup and a normal subgroup forms a subgroup -/
def prod (H : subgroup G) (K : normal G) : subgroup G := 
{ carrier := { g | ∃ h ∈ H, ∃ k ∈ K, g = h * k },
  one_mem' := ⟨1, one_mem H, 1, one_mem K, (group.one_mul _).symm⟩,
  mul_mem' := λ x y ⟨h₀, hh₀, k₀, hk₀, hx⟩ ⟨h₁, hh₁, k₁, hk₁, hy⟩,
    begin
      rw [hx, hy],
      refine ⟨h₀ * h₁, mul_mem H hh₀ hh₁, h₁⁻¹ * k₀ * h₁ * k₁, _, _⟩,
        { refine mul_mem K (mem_normal'.2 ⟨h₁, k₀, hk₀, rfl⟩) hk₁ },
        { simp [group.mul_assoc] }
    end,
  inv_mem' := λ x ⟨h, hh, k, hk, hx⟩,
    begin
      rw [hx, group.inv_mul],
      rw (show k⁻¹ * h⁻¹ = h⁻¹ * (h * k⁻¹ * h⁻¹), by simp [group.mul_assoc]),
      refine ⟨h⁻¹, inv_mem H hh, h * k⁻¹ * h⁻¹, 
        mem_normal.2 ⟨h, k⁻¹, inv_mem K hk, rfl⟩, by simp [group.mul_assoc]⟩      
    end } 

infix ` ⨯ `:70 := prod

lemma mem_product {H : subgroup G} {K : normal G} {x} : 
  x ∈ H ⨯ K ↔ ∃ (h ∈ H) (k ∈ K), x = h * k := iff.rfl

theorem product_eq_sup (H : subgroup G) (K : normal G) : H ⨯ K = H ⊔ K :=
begin
  ext, split,
    { intro hx, rcases mem_product.1 hx with ⟨h, hh, k, hk, rfl⟩,
      exact mul_mem _ (mem_sup_of_mem_left hh) (mem_sup_of_mem_right hk) },
    { revert x, 
      simp_rw [sup_def, closure_le'', mem_product],
      intros x hx, cases hx, 
        exact ⟨x, hx, 1, one_mem K, (group.mul_one x).symm⟩,
        exact ⟨1, one_mem H, x, hx, (group.one_mul x).symm⟩ }
end 

end product

-- We make a inductive type `subgroup_ge G H` which is the the type whose terms 
-- are subgroups of `G` greater than `H : subgroup G` (this makes sense since we 
-- created a lattice structure on subgroups). 

/-- `subgroup_ge G H` is the inductive type of subgroups of `G` thats greater 
  than `H`-/
inductive subgroup_ge (G : Type) [group G] (K : subgroup G) 
| mk (H : subgroup G) : (K ≤ H) → subgroup_ge

namespace ge

open subgroup_ge

-- We will show that the set of subgroups greater than some subgroup form a 
-- complete lattice. To do this we will use the fact that the subgroups forms 
-- a complete lattice and we will create a Galois insertion from subgroups 
-- inducing a complete lattice

@[simp] lemma subgroup_ge_eq (A B : subgroup G) {hA : H ≤ A} {hB : H ≤ B} : 
  subgroup_ge.mk A hA = subgroup_ge.mk B hB ↔ A = B := ⟨subgroup_ge.mk.inj, by cc⟩

instance : has_coe (subgroup_ge G H) (set G) := ⟨λ ⟨K, _⟩, (K : set G)⟩

@[simp] lemma ext' {A B : subgroup_ge G H} : 
  A = B ↔ (A : set G) = B :=
begin
  cases A, cases B,
  rw subgroup_ge_eq,
  exact ⟨by cc, λ h, ext' h⟩,
end

instance : has_mem G (subgroup_ge G H) := ⟨λ g K, g ∈ (K : set G)⟩

@[ext] theorem ext {A B : subgroup_ge G H}
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := ext'.2 $ set.ext h

instance has_coe_to_subgroup : has_coe (subgroup_ge G H) (subgroup G) := 
  ⟨λ ⟨K, _⟩, K⟩

@[simp] lemma subgroup_ge_eq' (A B : subgroup_ge G H) : 
  A = B ↔ (A : subgroup G) = B := by { cases A, cases B, exact subgroup_ge_eq _ _ }

-- We borrow the partital order structure from subgroups
instance : partial_order (subgroup_ge G H) := 
{ .. partial_order.lift (coe : subgroup_ge G H → subgroup G) $ λ x y hxy, by simp [hxy] }

instance : has_bot (subgroup_ge G H) := ⟨⟨H, le_refl _⟩⟩

instance : has_Inf (subgroup_ge G H) := 
⟨ λ s, subgroup_ge.mk (Inf { A | ∃ t ∈ s, (t : subgroup G) = A }) $ λ h hh,
  begin
    suffices : ∀ (i : subgroup G) (x : subgroup_ge G H), x ∈ s → ↑x = i → h ∈ ↑i,
      simpa [Inf],
    rintros _ ⟨t, ht⟩ _ rfl,
    exact ht hh
  end ⟩

lemma le_Inf (s : set (subgroup_ge G H)) : ∀ t ∈ s, Inf s ≤ t :=
begin
  rintros ⟨t, ht⟩ hst a ha,
  change a ∈ ⋂ t _, ↑t at ha,
  rw mem_bInter_iff at ha,
  exact ha t ⟨⟨t, ht⟩, hst, rfl⟩,
end  

def closure (A : subgroup G) : subgroup_ge G H := Inf { B | A ≤ B }

lemma closure_le (A : subgroup G) (B : subgroup_ge G H) : 
  closure A ≤ B ↔ A ≤ B :=
begin
  split,
    { intro h, cases B with B hB,
      exact le_trans 
        (show A ≤ _, by exact (λ _ ha, mem_bInter (λ _ ⟨⟨_, _⟩, ht', rfl⟩, ht' ha))) h },
    { intro h, exact le_Inf _ _ h }
end

lemma le_closure (A : subgroup_ge G H) : A = closure A :=
begin
  cases A with A hA,
  ext, split,
  { intro hx,
    refine mem_bInter (λ B hB, _),
    rcases hB with ⟨t, ht, rfl⟩,
    exact ht hx },
  { suffices : closure A ≤ ⟨A, hA⟩,
      intro hx, exact this hx,
    apply le_Inf,
    rw mem_set_of_eq,
    exact le_of_eq rfl }  
end

def gi : @galois_insertion (subgroup G) (subgroup_ge G H) _ _ closure (coe) := 
{ choice := λ x _, closure x,
  gc := λ A B, closure_le _ _,
  le_l_u := λ x, le_of_eq $ le_closure x,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subgroup_ge G H) := 
{.. @galois_insertion.lift_complete_lattice (subgroup G) (subgroup_ge G H) _ _ _ _ gi }

-- We can see easily that subgroup G is the same as subgroup_ge G ⊥

def subgroup_ge_bot_equiv : subgroup G ≃ subgroup_ge G ⊥ := 
{ to_fun := λ H, ⟨H, bot_le⟩,
  inv_fun := λ ⟨H, _⟩, H,
  left_inv := λ _, rfl,
  right_inv := λ ⟨_, _⟩, rfl }

def subgroup_ge_bot_order_iso : 
  let A := subgroup G in let B := subgroup_ge G ⊥ in 
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) :=
{ ord' := λ _ _, iff.rfl, 
  .. subgroup_ge_bot_equiv }

end ge

end subgroup

namespace lattice

/-- Given an equivalence `e` on preorders `A` and `B`, and a Galois connection 
  using `e`, there is an induced `order_iso` between `A` and `B`  -/
def order_iso_of_equiv_gi {A B : Type} [preorder A] [preorder B]
   (e : A ≃ B) (g : galois_connection e.to_fun e.inv_fun) : 
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) := 
{ ord' := λ a b, let h := g a (e.to_fun b) in
    by { rw e.left_inv at h, rw ←h, refl}, .. e }

open order_iso

/-- Given a `lattice`, `A`, there is an induced `lattice` on the `partial_order`, 
  `B` given that they are order isomorphic -/
def lattice_of_order_iso {A B : Type} [lattice A] [partial_order B] 
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : lattice B := 
{ .. galois_insertion.lift_lattice e.to_galois_insertion }

/-- Given a `lattice`, `B` and an `order_iso` to the `distrib_lattice`, `A`, 
  there is an induced `distrib_lattice` on `B` -/
def distrib_lattice_of_order_iso {A B : Type} [hA : distrib_lattice A] [lattice B]
  (e : ((≤) : B → B → Prop) ≃o ((≤) : A → A → Prop)) : distrib_lattice B := 
{ le_sup_inf := 
    begin
      intros x y z, rw e.ord',
      change e ((x ⊔ y) ⊓ (x ⊔ z)) ≤ e (x ⊔ y ⊓ z),
      rw [map_inf, map_sup, map_sup, map_sup, map_inf],
      apply hA.le_sup_inf
    end
  .. show lattice B, by apply_instance }

def distrib_lattice_of_order_iso' {A B : Type} [distrib_lattice A] [lattice B]
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : distrib_lattice B := 
distrib_lattice_of_order_iso $ order_iso.symm e

/-- Given a `distrib_lattice`, `A`, there is an induced `distrib_lattice` on the 
  `partial_order`, `B` given that they are order isomorphic -/
def distrib_lattice_of_order_iso'' {A B : Type} [distrib_lattice A] [partial_order B]
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : distrib_lattice B :=
@distrib_lattice_of_order_iso' _ _ _ 
  (@lattice_of_order_iso _ _ (distrib_lattice.to_lattice A) _ e) e

end lattice 

namespace normal 

instance : partial_order (normal G) := 
{.. partial_order.lift (normal.to_subgroup) (λ x y, normal.ext')}

instance : has_Inf (normal G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem',
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem' (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem' (by apply mem_bInter_iff.1 hx i h),
  conj_mem' := 
    begin
      simp_rw mem_bInter_iff,
      intros n hn g N hNs,
      exact N.conj_mem _ (hn N hNs) _, 
    end }⟩

@[simp] lemma mem_Inf (x : G) (s : set (normal G)) : 
  x ∈ Inf s ↔ x ∈ ⋂ t ∈ s, (t : set G) := iff.rfl

def closure (S : set G) : normal G := Inf {H | S ⊆ H}

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : normal G, S ⊆ H → x ∈ H := mem_bInter_iff

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : normal G) : closure S ≤ H ↔ S ≤ H :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y hy,
      change y ∈ (_ : normal G) at hy,
      unfold closure at hy,
      rw [mem_Inf, mem_bInter_iff] at hy,
      exact hy H h }
end

lemma closure_le' (S : set G) (H : normal G) : 
  (closure S : set G) ⊆ H ↔ S ⊆ H := closure_le S H

lemma closure_le'' (S : set G) (H : normal G) : 
  (∀ x, x ∈ closure S → x ∈ H) ↔ (∀ x, x ∈ S → x ∈ H) := closure_le S H

lemma closure_self {H : normal G} : closure (H : set G) = H :=
begin
  ext, split; intro hx,
    { apply subset.trans _ ((closure_le (H : set G) H).2 (subset.refl H)), 
      exact hx, exact subset.refl _ },
    { rw ← mem_carrier,
      apply subset.trans (le_closure (H : set G)), 
      intros g hg, assumption, assumption }
end

-- lemma closure_induction {p : G → Prop} {x} {k : set G} (h : x ∈ closure k)
--   (Hk : ∀ x ∈ k, p x) (H1 : p 1)
--   (Hmul : ∀ x y, p x → p y → p (x * y))
--   (Hinv : ∀ x, p x → p x⁻¹) : p x :=
-- (@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 Hk h

def gi : @galois_insertion (set G) (normal G) _ _ closure (λ H, H.carrier) :=
{ choice := λ S _, closure S,
  gc := λ H K,
    begin
      split; intro h,
        { exact subset.trans (le_closure H) h },
        { exact (closure_le _ _).2 h },
    end,
  le_l_u := λ H, le_closure (H : set G),
  choice_eq := λ _ _, rfl }

instance : complete_lattice (normal G) :=
{.. galois_insertion.lift_complete_lattice gi}

end normal

end mygroup
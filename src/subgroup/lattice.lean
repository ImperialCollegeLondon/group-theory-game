import subgroup.definitions

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

namespace mygroup

open group set

variables {G : Type} [group G]
variables {H K : subgroup G}

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

def closure (S : set G) : subgroup G := Inf {H | S ⊆ H}

/- We will now prove some lemmas that are helpful in proving subgroups 
form a galois_insertion with the coercion to set-/

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : subgroup G) : closure S ≤ H ↔ S ≤ (H : set G) :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y,
      unfold closure, unfold Inf, 
      rw mem_bInter_iff, intro hy,
      exact hy H h,
    }
end

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

end mygroup

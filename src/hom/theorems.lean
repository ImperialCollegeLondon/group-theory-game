import hom.definitions

/-
  The type of group homs G → H is
  denoted f : G →* H
  and the underlying function of types is ⇑f : G → H
  TODO: can we switch those arrows off?
  The axiom: if `f : G →* H` then `f.map_mul`
  is the assertion that for all a, b ∈ G
  we have f(a) = f(b). 
  Our first job is to prove `f.map_one` and `f.map_inv`.

  `f.map_one : f 1 = 1`
  `f.map_inv {x : G} : f (x⁻¹) = f(x)⁻¹`

-/

-- the entire project takes place in the mygroup namespace
namespace mygroup

-- We're proving things about group homs so this all goes in the `group_hom`
-- namespace

open set

namespace group_hom

variables {G H K : Type} [group G] [group H] [group K]

/-- If f is a group homomorphism then f 1 = 1. -/
@[simp] -- it's a good simp lemma
lemma map_one (f : G →* H) : f 1 = 1 :=
begin
  have h : f 1 * f 1 = f 1,
    rw ←f.map_mul,
    rw group.one_mul, -- annoying but stops cheating
    -- TODO: can I kill one_mul somehow? I asked on Zulip
  rw group.mul_left_eq_self at h, -- annoying
  assumption
end

/-- If f is a group homomorphism then f(x⁻¹) = f(x)⁻¹ -/
@[simp] -- it's also a good simp lemma
lemma map_inv (f : G →* H) {x : G} : f (x⁻¹) = (f x)⁻¹ :=
begin
  apply group.eq_inv_of_mul_eq_one,
  rw ←f.map_mul,
  rw group.mul_left_inv,
  rw f.map_one,
  -- refl
end

-- TODO: map and comap, kernel and image
-- We prove the theorems here (only);
-- definitions need to go elsewhere

-- Rather than defining the kernel as the preimage of {1}, I think defining it 
-- as a subgroup of the domain is better

-- We uses this and it should be moved to group
@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
by conv_rhs { rw [←(group.mul_left_inv (1 : G)), group.mul_one] }

/-- The kernel of a homomorphism `f : G →* H` is the subgroup of `G` whos carrier 
is the preimage of `{1}`, i.e. `f ⁻¹' {1}` -/
def kernel (f : G →* H) : subgroup G := 
{ carrier := f ⁻¹' {1},
  one_mem' := map_one _, 
  mul_mem' := 
    begin
      intros _ _ hx hy,
      rw [mem_preimage, mem_singleton_iff] at *,
      rw [map_mul f, hx, hy, group.mul_one]
    end,
  inv_mem' := 
    begin
      intros _ hx,
      rw [mem_preimage, mem_singleton_iff] at *,
      rw [map_inv f, hx, one_inv]
    end }

end group_hom

end mygroup

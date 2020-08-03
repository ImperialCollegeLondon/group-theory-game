import hom.quotient
import subgroup.lattice

local attribute [instance] classical.prop_decidable -- I hope we don't mind this

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

open set mygroup.subgroup

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

-- We prove the theorems here (only);
-- definitions need to go elsewhere

-- Rather than defining the kernel as the preimage of {1}, I think defining it 
-- as a subgroup of the domain is better

/-- The kernel of a homomorphism `f : G →* H` is the normal subgroup of `G` whos 
  carrier is the preimage of `{1}`, i.e. `f ⁻¹' {1}` -/
def kernel (f : G →* H) : normal G := 
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
      rw [map_inv f, hx, group.one_inv]
    end,
  conj_mem' :=
    begin
      intros _ hn _,
      rw [mem_preimage, mem_singleton_iff] at *,
      simp [hn],
    end }

/-- The image of a homomorphism `f : G →* H` is the subgroup of `H` whos carrier 
  is the image of `univ : set G`, i.e. `f '' univ` -/
def image (f : G →* H) : subgroup H :=
{ carrier := f '' univ, 
  one_mem' := ⟨1, mem_univ _, map_one _⟩,
  mul_mem' := 
    begin
      rintros _ _ ⟨x, hx₀, hx₁⟩ ⟨y, hy₀, hy₁⟩,
      refine ⟨x * y, mem_univ _, _⟩,
      rw [map_mul f x y, hx₁, hy₁]
    end, 
  inv_mem' := 
    begin
      rintros _ ⟨x, hx₀, hx₁⟩,
      refine ⟨x⁻¹, mem_univ _, _⟩,
      rw [←hx₁, map_inv]
    end }

variables {f : G →* H}

lemma mem_kernel {g : G} : g ∈ kernel f ↔ f g = 1 := 
  begin 
    split, intro h,
    apply mem_singleton_iff.1,
    apply mem_preimage.1,
    exact h,
    intro h,
    apply mem_singleton_iff.1,
    apply mem_singleton_iff.2, exact h,
  end
 -- ⟨λ h, mem_singleton_iff.1 $ mem_preimage.1 h, λ h, h⟩

lemma mem_kernel_of_eq {f : G →* H} {a b : G} (h : f a = f b) : 
  b⁻¹ * a ∈ kernel f := 
begin
  rw [← group.mul_left_cancel_iff (f b⁻¹), ← map_mul] at h,
  symmetry' at h, 
  rw ← map_mul at h, 
  rw [group.mul_left_inv, map_one] at h,
  apply mem_singleton_iff.1,
  apply mem_preimage.1, 
  apply mem_singleton_iff.2,
  symmetry, exact h,
--original proof
  /-rw [mem_kernel, map_mul, map_inv, 
    ←group.mul_left_cancel_iff (f b)],
  simp [←mul_assoc, h]-/
end
    
lemma mem_image {h : H} : h ∈ image f ↔ ∃ g, f g = h := 
begin 
  refine ⟨λ himg, _, λ himg, _⟩,
    { rcases (mem_image f univ h).1 himg with ⟨g, _, hg⟩,
      exact ⟨g, hg⟩ },
    { rcases himg with ⟨g, hg⟩,
      show h ∈ f '' univ,
      refine (mem_image f _ _).2 ⟨g, mem_univ g, hg⟩ }
end

attribute [simp] mem_kernel mem_image

-- We will prove the classic results about injective homomorphisms that a 
-- homomorphism is injective if and only if it have the trivial kernel

open function

/-- A homomorphism `f` is injective iff. `f` has kernel `{1}` -/
theorem injective_iff_ker_eq_one : 
  injective f ↔ (kernel f : set G) = {1} :=
begin -- Should we split this up into maby smaller proofs or should we keep it?

 --Was trying to rewrite proof differently, need to ask some things
/-split; intro hf,
  unfold injective at hf,
  have h : ∀ {a b : G},  f a = f b → (b⁻¹*a) ∈ kernel f,
    { intros a b h1,
      apply mem_kernel_of_eq,
      exact h1,
    }, -/
  
  split; intro hf,
    { show f ⁻¹' {1} = {1},
      ext, split; intro hx,
        { apply @hf x 1,
          rw map_one, 
          exact mem_singleton_iff.1 hx },
        { rw [mem_preimage, mem_singleton_iff, mem_singleton_iff.1 hx],
          exact map_one _ } },
    { change f ⁻¹' {1} = {1} at hf,
      by_contra h, push_neg at h,
      rcases h with ⟨x, y, heq, hneq⟩,
      refine hneq (group.mul_right_cancel y⁻¹ _ _ _),
      have : x * y⁻¹ ∈ f ⁻¹' {1},
        apply group.mul_right_cancel (f y),
        rw [map_mul f, group.mul_assoc, map_inv, group.mul_left_inv, 
            group.one_mul, group.mul_one, heq],
      rw [hf, mem_singleton_iff] at this, 
      rw [this, group.mul_right_inv] }
end

/-- A homomorphism `f : G →* H` is surjective iff. the image of `f` is `H` -/
theorem surjective_iff_max_img : 
  surjective f ↔ (image f : set H) = univ :=
begin
  split; intro hf,
    { ext y, split; intro hy,
        exact mem_univ _,
        cases hf y with x hx,
        refine ⟨x, mem_univ _, hx⟩ },
    { intro y,
      rcases (show y ∈ (image f : set H), 
        by rw hf; exact mem_univ _) with ⟨x, _, hx⟩,
      exact ⟨x, hx⟩ }
end

end group_hom

-- pushforward and pullback of subgroups

namespace subgroup

open set

variables {G : Type} [group G] {H : Type} [group H]

/-- image of a subgroup is a subgroup -/
def map (f : G →* H) (K : subgroup G) : subgroup H :=
{ carrier := f '' (K.carrier),
  one_mem' := begin
    rw mem_image,
    use 1,
    split,
    { exact K.one_mem},
    { exact f.map_one}
  end,
  mul_mem' := begin
    rintros _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩,
    refine ⟨a*b, K.mul_mem ha hb, f.map_mul _ _⟩,
  end,
  inv_mem' := begin
    rintros _ ⟨a, ha, rfl⟩,
    refine ⟨a⁻¹, K.inv_mem ha, f.map_inv⟩,
  end }

lemma mem_map (f : G →* H) (K : subgroup G) (a : H) :
  a ∈ K.map f ↔ ∃ g : G, g ∈ K ∧ f g = a := iff.rfl

end subgroup

namespace quotient

open group_hom lagrange mygroup.quotient function

variables {G H K : Type} [group G] [group H] [group K]

variable {f : G →* H}

/-- The natural map from a group `G` to its quotient `G / N` is a homomorphism -/
def mk (N : normal G) : G →* G /ₘ N := 
{ to_fun := λ g, g,
  map_mul' := λ _ _, by apply quotient.sound; refl }

variable {N : normal G}

/-- The natural homomorphism from a group `G` to its quotient `G / N` is a 
  surjection -/
theorem is_surjective : surjective $ mk N := exists_mk

-- The first isomorphism theorem states that for all `f : G →* H`, 
-- `G /ₘ kernel f ≅ image f`, we will prove this here.

-- We will use `lift_on` which is the same as `quotient.lift_on'`
-- Given an equivalence relation `R` on some type `α`, and a function `f : α → β`
-- `λ (a : quotient R), quotient.lift_on' a f h` is the function that maps `⟦x⟧` 
-- to `f x` where `h` is a proof that this function is well defined, i.e. 
-- `∀ x y : α, ⟦x⟧ = ⟦y⟧ → f x = f y`.

-- First we prove such a map is well defined 
lemma map_of_lcoset_eq {f : G →* H} {x y : G} 
  (hxy : x • kernel f = y • kernel f) : f x = f y :=
begin
  rw [←group.mul_left_cancel_iff (f y)⁻¹, 
      ←map_inv, ←map_mul, map_inv, group.mul_left_inv,
      ←mem_kernel],
  exact lcoset_eq.1 hxy
end 

/-- Given a group homomorphism `f : G →* H`, `kernel_lift f` is a mapping from 
  the quotient `G /ₘ kernel f` to `H` such that `x • kernel f ↦ f x` -/
def kernel_lift (f : G →* H) (x : G /ₘ kernel f) := lift_on x f $ 
  λ _ _, map_of_lcoset_eq

@[simp] lemma kernel_lift_mk {f : G →* H} (g : G) :
  kernel_lift f (g : G /ₘ kernel f) = f g := rfl

/-- Given a group homomorphism `f : G →* H`, `kernel_lift f` form a homomorphism 
  `kernel_lift_hom f` from `(G /ₘ kernel f) →* H` -/
def kernel_lift_hom (f : G →* H) : (G /ₘ kernel f) →* H := 
{ to_fun := kernel_lift f,
  map_mul' := λ x y, quotient.induction_on₂' x y $ λ _ _,
    by simp only [quotient.coe, quotient.coe_mul, kernel_lift_mk, map_mul] }

/-- `kernel_lift_hom f` is an injective homomorphism -/
lemma injective_of_kernel_lift_hom {f : G →* H} : 
  injective $ kernel_lift_hom f :=
begin
  intros x y,
  apply quotient.induction_on₂' x y,
  intros _ _ hab,
  change kernel_lift f a₁ = kernel_lift f a₂ at hab,
  iterate 2 { rw kernel_lift_mk at hab, rw quotient.coe },
  rw [mk_eq, lcoset_eq],
  exact mem_kernel_of_eq hab 
end

/-- An alternative to `kernel_lift_hom` in which the range is restricted to the 
  image of `f` so that the homomorphism is also surjective -/
def kernel_lift_hom' (f : G →* H) : (G /ₘ kernel f) →* f.image :=
{ to_fun := λ q, ⟨kernel_lift f q, quotient.induction_on' q $ 
    λ a, show f a ∈ f.image, by exact ⟨a, mem_univ _, rfl⟩⟩,
  map_mul' := λ x y, quotient.induction_on₂' x y $ λ _ _,
    by simpa only [quotient.coe, quotient.coe_mul, kernel_lift_mk, map_mul] }

lemma kernel_lift_hom'_eq_kernel_lift_hom {f : G →* H} (q : G /ₘ kernel f) : 
  (kernel_lift_hom' f q : H) = kernel_lift_hom f q := rfl

lemma injective_of_kernel_lift_hom' {f : G →* H} : 
  injective $ kernel_lift_hom' f := λ x y hxy, injective_of_kernel_lift_hom $
by iterate 2 { rw ←kernel_lift_hom'_eq_kernel_lift_hom }; rw hxy

lemma surjective_of_kernel_lift_hom' {f : G →* H} : 
  surjective $ kernel_lift_hom' f := λ ⟨_, x, _, rfl⟩, ⟨x, kernel_lift_mk x⟩

/-- Given a group homomorphism `f`, `kernel_lift_hom' f` is a bijection -/
lemma bijective_of_kernel_lift_hom' {f : G →* H} :
  bijective $ kernel_lift_hom' f := 
⟨injective_of_kernel_lift_hom', surjective_of_kernel_lift_hom'⟩

/-- The first isomorphism theorem: `G /ₘ kernel f ≅ image f` for `f : G →* H` 
  a group homomorphism -/
def quotient_kernel_iso_image (f : G →* H) : 
  G /ₘ kernel f ≅ image f := 
{ is_bijective := bijective_of_kernel_lift_hom',
  .. kernel_lift_hom' f }

-- Inclusion map as a homomorphism from a subgroup to the group
def 𝒾 (H : subgroup G) : H →* G := 
{ to_fun := λ h, (h : G),
  map_mul' := λ _ _, rfl } 

@[simp] lemma 𝒾_def {H : subgroup G} {h} (hh : h ∈ H) : 𝒾 H ⟨h, hh⟩ = h := rfl

-- The inclusion map is injective 
lemma injective_𝒾 {H : subgroup G} : injective $ 𝒾 H := λ _ _ hxy, subtype.eq hxy

-- The image of a surjective homomorphism is isomorphic to the group its mapped to
def iso_of_surjective {f : G →* H} (hf : surjective f) : image f ≅ H :=
{ is_bijective := ⟨ injective_𝒾, λ y,
    ⟨⟨y, show y ∈ f '' univ, by simp [hf y]⟩, by simp [𝒾]⟩ ⟩,
  .. 𝒾 $ image f }

end quotient

namespace normal

open group_hom function mygroup.quotient

variables {G H : Type} [group G] [group H]

/-- The preimage of a normal subgroup is normal -/
def comap (f : G →* H) (N : normal H) : normal G := 
{carrier := f⁻¹' N,
 one_mem' := 
    begin
      rw [mem_preimage, map_one],
      exact N.one_mem', 
    end,
 mul_mem' :=
    begin
      intros x y h1 h2,
      rw mem_preimage at *,
      rw map_mul,
      exact N.mul_mem' h1 h2,
    end,
 inv_mem' := 
    begin
      intros x h,
      rw [mem_preimage] at *,
      rw map_inv,
      exact N.inv_mem' h,
    end,
 conj_mem' := 
    begin
      intros n h t ,
      rw [mem_preimage, map_mul, map_mul],
      rw mem_preimage at h,
      show _ ∈ N,
      convert N.conj_mem (f n) h (f t), 
      apply f.map_inv
    end }

/-- The surjective image of a normal subgroup is normal -/
def nmap {f : G →* H} (hf : surjective f) (N : normal G) : normal H := 
{ carrier := f '' N,
  one_mem' := ⟨1, N.to_subgroup.one_mem, f.map_one⟩,
  mul_mem' := 
    begin
      rintros _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩,
      refine ⟨a * b, N.to_subgroup.mul_mem ha hb, f.map_mul a b⟩,
    end,
  inv_mem' := 
    begin
      rintros _ ⟨a, ha, rfl⟩,
      refine ⟨a⁻¹, N.to_subgroup.inv_mem ha, f.map_inv⟩,    
    end,
  conj_mem' := 
    begin
      rintro _ ⟨b, hb, rfl⟩,
      intro h,
      dsimp,
      rcases hf h with ⟨g, rfl⟩,
      use g * b * g⁻¹,
      split,
      { exact N.conj_mem b hb g},
      { simp [f.map_mul] }
    end }

/-- Intersection of T and N is the pushforward to G of (the pullback to T of N) 
along the natural map T → G -/
theorem subgroup_inf (N : normal G) (T : subgroup G) : 
  (T ⊓ N) = subgroup.map (𝒾 T) (comap (𝒾 T) N) :=
begin
  ext x,
  split,
  { intro h,
    rw mem_inf at h,
    rw subgroup.mem_map,
    cases h with hxt hxn,
    use ⟨x, hxt⟩,
    split,
    { show _ ∈ ⇑(𝒾 T) ⁻¹' ↑N,
      exact hxn },
    { refl } },
  { rintro ⟨⟨g, hgt⟩, ht1, rfl⟩,
    change g ∈ T at hgt,
    rw mem_inf,
    split,
    { exact hgt },
    { exact ht1 } }
end

end normal

namespace quotient

variables {G H : Type} [group G] [group H]

def second_iso_theorem (T : subgroup G) (N : normal G) : 
  T /ₘ (N.comap (𝒾 T)) ≅ ↥(T ⊔ N) /ₘ N.comap (𝒾 (T ⊔ N)) :=
{ to_fun := sorry,
  map_mul' := sorry,
  is_bijective := sorry }

-- to state this one we need to be able to push forward (`map`) a normal
-- subgroup along a surjection

def third_iso_theorem (T : normal G) (N : normal G)
  (h : T.carrier ⊆ N.carrier) :
  let NmodT : normal (G /ₘ T) := N.nmap (quotient.is_surjective) in  
   (G /ₘ T) /ₘ NmodT ≅ G /ₘ N := sorry

end quotient

end mygroup

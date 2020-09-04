import subgroup.lattice

/-!

Group homomorphisms

-/

-- We're always overwriting group theory here so we always work in
-- a namespace
namespace mygroup

/- homomorphisms of groups -/

/-- Bundled group homomorphisms -/
structure group_hom (G H : Type) [group G] [group H] :=
(to_fun : G → H)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

-- notation
infixr ` →* `:25 := group_hom

-- coercion to a function
instance {G H : Type} [group G] [group H] :
  has_coe_to_fun (G →* H) := ⟨_, group_hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {G H : Type} [group G] [group H]
  (f : G →* H) : f.to_fun = f := rfl

@[ext] lemma ext_hom {G H : Type} [group G] [group H] (φ ψ : G →* H) : 
  φ = ψ ↔ φ.to_fun = ψ.to_fun := 
begin
 split, { cc }, 
  { intro h,
    cases φ with φ1 φ2,
    cases ψ with ψ1 ψ2,
    simp * at * }
end

@[ext] lemma ext {G H : Type} [group G] [group H] (φ ψ : G →* H)
  (h : ∀ g : G, φ g = ψ g) : φ = ψ :=
begin
  rw ext_hom,
  ext g,
  exact h g,  
end

-- the identity homomorphism
def id_hom {G : Type} [group G] : G →* G := ⟨id, λ x y, rfl⟩

/-- Group isomorphism as a bijective group homomorphism -/
structure group_iso (G H : Type) [group G] [group H] extends group_hom G H :=
(is_bijective : function.bijective to_fun)
notation G ` ≅ ` H := group_iso G H

-- Coercion from `group_iso` to `group_hom`
instance {G H : Type} [group G] [group H] : 
  has_coe_t (G ≅ H) (G →* H) := ⟨group_iso.to_group_hom⟩

instance coe_iso_to_fun {G H : Type} [group G] [group H] :
  has_coe_to_fun (G ≅ H) := ⟨_, group_iso.to_group_hom⟩

-- Should we define it this way or as an extension of equiv that preserves mul? 

/- Alternative definition
structure group_equiv (G H : Type) [group G] [group H] extends G ≃ H :=
(map_mul' : ∀ x y : G, to_fun (x * y) = to_fun x * to_fun y) 

notation G ` ≅ ` H := group_equiv G H

-- Coercion from `group_equiv` to `group_hom`
instance {G H : Type} [group G] [group H] : 
  has_coe (G ≅ H) (G →* H) := ⟨λ f, ⟨f.to_fun, f.map_mul'⟩⟩ -/

open set mygroup.subgroup function

namespace group_hom

variables {G H K : Type} [group G] [group H] [group K]

/-- If f is a group homomorphism then f (a * b) = f a * f b. -/
@[simp]
lemma map_mul (f : G →* H) (a b : G) : f (a * b) = f a * f b :=
f.map_mul' a b

/-- The composition of two group homomorphisms form a group homomorphism -/
def map_comp (f : G →* H) (g : H →* K) : G →* K := 
{ to_fun   := g ∘ f, 
  map_mul' := λ x y, by simp }
notation g ` ∘* ` f := map_comp f g

@[simp] lemma coe_map_comp (f : G →* H) (g : H →* K) : ((g ∘* f) : G → K) =
  g ∘ f := rfl

/-- A group is isomorphic to itself by the identity homomorphism -/
def iso_refl : G ≅ G := 
{ is_bijective := function.bijective_id, .. id_hom }

/-- The composition of two group isomorphisms form a group isomorphism -/
def iso_comp (f : G ≅ H) (g : H ≅ K) : G ≅ K := 
{ is_bijective := function.bijective.comp g.is_bijective f.is_bijective,
  .. (g : group_hom H K) ∘* (f : group_hom G H) }

/-- An equiv between two groups that preserves multiplication forms an isomorphism -/
def iso_of_mul_equiv (f : G ≃* H) : G ≅ H := 
{ to_fun := f, map_mul' := f.map_mul',
  is_bijective := equiv.bijective f.to_equiv }

/-- An isomorphism between two groups from an mul_equiv -/
noncomputable def mul_equiv_of_iso (f : G ≅ H) : G ≃* H := 
{ map_mul' := map_mul f, .. equiv.of_bijective _ f.is_bijective }

/-- If the group `G` is isomorphic to the group `H`, then `H` is isomorphic to `G`-/
noncomputable def iso_symm (f : G ≅ H) : H ≅ G := 
  iso_of_mul_equiv $ mul_equiv.symm $ mul_equiv_of_iso f

def to_prod (H : subgroup G) (N : normal G) : H →* H ⨯ N :=
{ to_fun := λ h, ⟨h.1, h.1, h.2, 1, subgroup.one_mem N, (group.mul_one _).symm⟩,
  map_mul' := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.val_injective rfl }

@[simp] lemma to_prod_apply (H : subgroup G) (N : normal G) (h : H) :
  to_prod H N h = ⟨h.1, h.1, h.2, 1, subgroup.one_mem N, (group.mul_one _).symm⟩ :=
rfl

@[simp] lemma to_prod_mul {H : subgroup G} {K : normal G} (x y : H) :
  (to_prod H K x) * (to_prod H K y) = to_prod H K (x * y) := rfl

def to_prod' (H : subgroup G) (N : normal G) : N.to_subgroup →* H ⨯ N :=
{ to_fun := λ n, ⟨n.1, 1, H.one_mem, n.1, n.2, (group.one_mul _).symm⟩,
  map_mul' := λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.val_injective rfl }

open_locale classical

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

-- Inclusion map as a homomorphism from a subgroup to the group
def 𝒾 (H : subgroup G) : H →* G :=
{ to_fun := λ h, (h : G),
  map_mul' := λ _ _, rfl }

@[simp] lemma 𝒾_def {H : subgroup G} {h} (hh : h ∈ H) : 𝒾 H ⟨h, hh⟩ = h := rfl

-- The inclusion map is injective
lemma injective_𝒾 {H : subgroup G} : injective $ 𝒾 H := λ _ _ hxy, subtype.eq hxy

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

/-- The image of a homomorphism `f : G →* H` is the subgroup of `H` whose carrier
  is the image of `univ : set G`, i.e. `f '' univ` -/
def image (f : G →* H) : subgroup H :=
{ carrier := range f,
  one_mem' := ⟨1, map_one _⟩,
  mul_mem' := λ _ _ ⟨x, hx₁⟩ ⟨y, hy₁⟩, ⟨x * y, by rw [map_mul f x y, hx₁, hy₁]⟩,
  inv_mem' := λ _ ⟨x, hx₁⟩, ⟨x⁻¹, by rw [←hx₁, map_inv]⟩ }

variables {f : G →* H}

lemma mem_kernel {g : G} : g ∈ kernel f ↔ f g = 1 :=
  ⟨λ h, mem_singleton_iff.1 $ mem_preimage.1 h, λ h, h⟩

lemma mem_kernel_of_eq {a b : G} (h : f a = f b) :
  b⁻¹ * a ∈ kernel f :=
begin
  rw [mem_kernel, map_mul, map_inv,
    ←group.mul_left_cancel_iff (f b)],
  simp [←mul_assoc, h]
end

lemma one_mem_kernel (f : G →* H) : (1 : G) ∈ kernel f := map_one f

lemma mem_image {h : H} : h ∈ image f ↔ ∃ g, f g = h := iff.rfl

attribute [simp] mem_kernel mem_image

-- We will prove the classic results about injective homomorphisms that a
-- homomorphism is injective if and only if it have the trivial kernel

/-- A homomorphism `f` is injective iff. `f` has kernel `{1}` -/
theorem injective_iff_kernel_eq_one :
  injective f ↔ (kernel f : set G) = {1} :=
begin
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

theorem injective_iff_kernel_eq_one' :
  injective f ↔ ∀ a, f a = 1 → a = 1 :=
begin
  rw injective_iff_kernel_eq_one,
  simp_rw [←mem_kernel, set.ext_iff, mem_singleton_iff],
  split,
  { intros h a ha,
    rwa ←h },
  { intros h a,
    split, apply h,
    rintro rfl,
    apply one_mem }
end

/-- A homomorphism `f : G →* H` is surjective iff. the image of `f` is `H` -/
theorem surjective_iff_max_img :
  surjective f ↔ (image f : set H) = univ :=
begin
  split; intro hf,
    { ext y, exact ⟨λ _, mem_univ _, λ hy, hf y⟩ },
    { intro y,
      exact (show y ∈ (image f : set H), by rw hf; exact mem_univ _) }
end

end group_hom 

namespace subgroup

-- pushforward and pullback of subgroups

variables {G : Type} [group G] {H : Type} [group H]

/-- The image of a subgroup under a group homomorphism is a subgroup -/
def map (f : G →* H) (K : subgroup G) : subgroup H :=
{ carrier := f '' K,
  one_mem' := by rw mem_image; exact ⟨1, K.one_mem, f.map_one⟩,
  mul_mem' := by rintros _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩;
    exact ⟨a * b, K.mul_mem ha hb, f.map_mul _ _⟩,
  inv_mem' := by rintros _ ⟨a, ha, rfl⟩; exact ⟨a⁻¹, K.inv_mem ha, f.map_inv⟩ }

lemma mem_map (f : G →* H) (K : subgroup G) (a : H) :
  a ∈ K.map f ↔ ∃ g : G, g ∈ K ∧ f g = a := iff.rfl

/-- The preimage of a subgroup under a group homomorphism is a subgroup -/
def comap (f : G →* H) (K : subgroup H) : subgroup G := 
{ carrier := f ⁻¹' K,
  one_mem' := show f 1 ∈ K, by rw f.map_one; exact one_mem K,
  mul_mem' := λ x y hx hy, show f (x * y) ∈ K, 
    by rw f.map_mul; exact mul_mem K hx hy,
  inv_mem' := λ x hx, show f x⁻¹ ∈ K, by rw f.map_inv; exact inv_mem K hx }

lemma mem_comap' (f : G →* H) (M : subgroup H) (g : G) :
  g ∈ M.comap f ↔ f g ∈ M := iff.rfl

def gc (f : G →* H) : galois_connection (map f) (comap f) :=
begin
  rintros A B,
  show f.to_fun '' A.carrier ⊆ B.carrier ↔ A.carrier ⊆ f.to_fun ⁻¹' B.carrier,
  finish
end

theorem closure_image (f : G →* H) (S : set G) :
  closure (f '' S) = map f (closure S) :=
begin
  apply lattice.le_antisymm,
  { rw [closure_le, le_eq_subset, image_subset_iff],
    refine subset.trans (le_closure _) _,
    change closure S ≤ comap f (map f (closure S)),
    apply galois_connection.le_u_l (gc f) },
  { refine galois_connection.l_le (gc f) _,
    rw closure_le,
    have h : S ⊆ f ⁻¹' ( f '' S),
      intro x, finish,
    refine set.subset.trans h _,
    show f ⁻¹' _ ⊆ f ⁻¹' _,
    mono, apply le_closure }
end

theorem closure_singleton (f : G →* H) (g : G) :
  closure ({f g} : set H) = map f (closure ({g})) :=
by convert closure_image f ({g} : set G); finish

end subgroup

namespace normal

open group_hom mygroup.subgroup

variables {G H : Type} [group G] [group H]

/-- The preimage of a normal subgroup under a group homomorphism is normal -/
def comap (f : G →* H) (N : normal H) : normal G :=
{carrier := f ⁻¹' N,
 one_mem' := by rw [mem_preimage, map_one]; exact N.one_mem',
 mul_mem' := λ _ _ h₁ h₂, mem_preimage.2 (by rw map_mul; exact N.mul_mem' h₁ h₂),
 inv_mem' := λ _ h, mem_preimage.2 (by rw map_inv; exact N.inv_mem' h),
 conj_mem' :=
    begin
      intros n h t ,
      rw [mem_preimage, map_mul, map_mul],
      change _ ∈ N, convert N.conj_mem (f n) h (f t),
      apply f.map_inv
    end }

@[simp] lemma mem_comap {f : G →* H} {N : normal H} (x) : 
  x ∈ comap f N ↔ f x ∈ N := 
show x ∈ f ⁻¹' N ↔ f x ∈ N, by exact mem_preimage

/-- The surjective image of a normal subgroup is normal -/
def nmap {f : G →* H} (hf : surjective f) (N : normal G) : normal H :=
{ carrier := f '' N,
  one_mem' := ⟨1, N.to_subgroup.one_mem, f.map_one⟩,
  mul_mem' := by rintros _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩;
      exact ⟨a * b, N.to_subgroup.mul_mem ha hb, f.map_mul a b⟩,
  inv_mem' := by rintros _ ⟨a, ha, rfl⟩;
      exact ⟨a⁻¹, N.to_subgroup.inv_mem ha, f.map_inv⟩,
  conj_mem' :=
    begin
      rintro _ ⟨b, hb, rfl⟩ h,
      rcases hf h with ⟨g, rfl⟩,
      exact ⟨g * b * g⁻¹, N.conj_mem b hb g, by simp [f.map_mul]⟩
    end }

@[simp] lemma mem_nmap {f : G →* H} (hf : surjective f) {N : normal G} (y) : 
  y ∈ nmap hf N ↔ ∃ x ∈ N, f x = y := 
  show y ∈ f '' N ↔ _, by rw mem_image_iff_bex; refl

/-- Intersection of T and N is the pushforward to G of (the pullback to T of N)
along the natural map T → G -/
theorem subgroup_inf (N : normal G) (T : subgroup G) :
  (T ⊓ N) = map (𝒾 T) (comap (𝒾 T) N) :=
begin
  ext x, split,
  { exact λ h, let ⟨hxt, hxn⟩ := mem_inf.1 h in 
      (mem_map _ _ _).1 ⟨⟨x, hxt⟩, hxn, rfl⟩ },
  { rintro ⟨⟨g, hgt⟩, ht1, rfl⟩, exact mem_inf.2 ⟨hgt, ht1⟩ }
end

end normal

end mygroup
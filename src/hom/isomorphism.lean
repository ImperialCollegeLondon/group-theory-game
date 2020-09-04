import subgroup.lagrange

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

-- the entire project takes place in the mygroup namespace
namespace mygroup

open group_hom lagrange mygroup.quotient normal
  function set mygroup.subgroup

namespace quotient

variables {G H K : Type} [group G] [group H] [group K]
variables {f : G →* H}

/-- The natural map from a group `G` to its quotient `G / N` is a homomorphism -/
def mk (N : normal G) : G →* G /ₘ N :=
{ to_fun := λ g, g,
  map_mul' := λ _ _, by apply quotient.sound; refl }

variable {N : normal G}

-- The coercion from `G` to `G /ₘ N` is exactly our `mk` group hom
@[simp] lemma coe_eq_mk (g : G) : (g : G /ₘ N) = mk N g := rfl

-- The kernel of `mk N` is `N` 
lemma kernel_mk {N : normal G} : kernel (mk N) = N :=
begin
  ext x,
  show (x : G /ₘ N) = (1 : G) ↔ x ∈ N.to_subgroup,
  rw [mk_eq, ←con_one_iff_mem],
  refl,
end

/-- The natural homomorphism from a group `G` to its quotient `G / N` is a
  surjection -/
theorem is_surjective_mk : surjective $ mk N := exists_mk

-- The first isomorphism theorem states that for all `f : G →* H`,
-- `G /ₘ kernel f ≅ image f`, we will prove this here.

-- We will use `lift_on` which is the same as `quotient.lift_on'`
-- Given an equivalence relation `R` on some type `α`, and a function `f : α → β`
-- `λ (a : quotient R), quotient.lift_on' a f h` is the function that maps `⟦x⟧`
-- to `f x` where `h` is a proof that this function is well defined, i.e.
-- `∀ x y : α, ⟦x⟧ = ⟦y⟧ → f x = f y`.

/- Given a group hom `f : G →* H` and a normal subgroup `N` of `G`
with `N ⊆ kernel f`, there's an induced hom `G /ₘ N → H` -/
def lift (f : G →* H) (N : normal G) (h : N.to_subgroup ≤ kernel f) :
G /ₘ N →* H :=
{ to_fun := λ x, lift_on x f 
  begin
    intros x y h1,
    rw [con_of_normal_def, lcoset_rel_def, lcoset_eq] at h1,
    specialize h h1,
    change y⁻¹ * x ∈ f.kernel at h,
    rw mem_kernel at h,
    rw [map_mul, map_inv] at h,
    apply group.mul_left_cancel (f y)⁻¹,
    rw h, simp
  end,
  map_mul' := λ a b, quotient.induction_on₂' a b f.map_mul }

@[simp] lemma lift_mk {f : G →* H} (N : normal G) (h : N.to_subgroup ≤ kernel f)
  (g : G) : lift f N h (mk N g) = f g := rfl

lemma lift_image {f : G →* H} {N : normal G} (h : N.to_subgroup ≤ kernel f) :
  (lift f N h).image = f.image :=
begin
  ext x, split,
  { rintro ⟨a, rfl⟩,
    rcases exists_mk a with ⟨g, rfl⟩,
    exact group_hom.mem_image.2 ⟨g, rfl⟩ },
  { rintro ⟨a, rfl⟩,
    exact ⟨(mk N a), rfl⟩ }
end

-- For the first isomorphism theorem, we will define a specific version of the
-- `lift` homomorphism above with `N = kernel f` 

-- First we prove such a map is well defined
lemma map_of_lcoset_eq {f : G →* H} {x y : G}
  (hxy : x ⋆ kernel f = y ⋆ kernel f) : f x = f y :=
begin
  rw [←group.mul_left_cancel_iff (f y)⁻¹,
      ←map_inv, ←map_mul, map_inv, group.mul_left_inv,
      ←mem_kernel],
  exact lcoset_eq.1 hxy
end

/-- Given a group homomorphism `f : G →* H`, `kernel_lift f` is a mapping from
  the quotient `G /ₘ kernel f` to `H` such that `x ⋆ kernel f ↦ f x` -/
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
    λ a, show f a ∈ f.image, by exact ⟨a, rfl⟩⟩,
  map_mul' := λ x y, quotient.induction_on₂' x y $ λ _ _,
    by simpa only [quotient.coe, quotient.coe_mul, kernel_lift_mk, map_mul] }

lemma kernel_lift_hom'_eq_kernel_lift_hom {f : G →* H} (q : G /ₘ kernel f) :
  (kernel_lift_hom' f q : H) = kernel_lift_hom f q := rfl

lemma injective_of_kernel_lift_hom' {f : G →* H} :
  injective $ kernel_lift_hom' f := λ x y hxy, injective_of_kernel_lift_hom $
by iterate 2 { rw ←kernel_lift_hom'_eq_kernel_lift_hom }; rw hxy

lemma surjective_of_kernel_lift_hom' {f : G →* H} :
  surjective $ kernel_lift_hom' f := λ ⟨_, x, rfl⟩, ⟨x, kernel_lift_mk x⟩

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

-- The image of a surjective homomorphism is isomorphic to the group its mapped to
def iso_of_surjective {f : G →* H} (hf : surjective f) : image f ≅ H :=
{ is_bijective := ⟨ injective_𝒾, λ y,
    ⟨⟨y, show y ∈ range f, by simp [hf y]⟩, by simp [𝒾]⟩ ⟩,
  .. 𝒾 $ image f }

/-- The first isomorphism theorem with a surjective homomorphism:
  `G /ₘ kernel f ≅ H` for `f : G →* H` a surjective group homomorphism-/
def quotient_kernel_iso_of_surjective {f : G →* H} (hf : surjective f) :
  G /ₘ kernel f ≅ H :=
iso_comp (quotient_kernel_iso_image f) $ iso_of_surjective hf

def subst_iso {A B : normal G} (h : A = B) : G /ₘ A ≅ G /ₘ B :=
{ is_bijective := begin subst h, convert bijective_id, ext x, rcases x, refl end,
  ..(lift (mk B) A (by {rw [h, kernel_mk], refl'})) }

def subst_iso' {A B : normal G} (h : A = B) (f : G /ₘ A ≅ H) : G /ₘ B ≅ H := 
iso_comp (subst_iso h.symm) f

def quotient_kernel_iso_of_surjective' {f : G →* H} (hf : surjective f) 
{N : normal G} (hN : kernel f = N) :
  G /ₘ N ≅ H := subst_iso' hN $ quotient_kernel_iso_of_surjective hf

/-- If `N ⊆ kernel f` then the kernel of induced map `lift f N h` is 
  image of `kernel f` -/
lemma lift_kernel {f : G →* H} {N : normal G} (h : N.to_subgroup ≤ kernel f) :
  kernel (lift f N h) = nmap is_surjective_mk (kernel f) :=
begin
  ext x, split,
  { intro h2, rcases quotient.exists_mk x with ⟨g, rfl⟩,
    rw coe_eq_mk at *, rw [mem_kernel, lift_mk] at h2,
    refine ⟨g, mem_kernel.2 h2, rfl⟩ },
  { rintro ⟨g, hg1, rfl⟩,
    change g ∈ f.kernel at hg1,
    rw mem_kernel at *, rw lift_mk, assumption }
end

/-
  The way to think about the formulation of the second isomorphism theorem is
  think about the individual mappings.

  First let us think about what `comap (𝒾 T) N` represents.
  `comap f N` is the normal subgroup whose underlying set is the preimage of `N`
  alongside `f`, so `comap (𝒾 T) N` is the normal subgroup of `T` that gets
  mapped into `N` under the inclusion map, i.e. elements in `T ∩ N`.

  Now let us consider `comap (𝒾 (T ⊔ N)) N` which is similar.

  Again the the `comap (𝒾 (T ⊔ N)) N` is the preimage along the inclusion map
  `𝒾 (T ⊔ N)`. But this this time we see that `N ⊆ T ⊔ N`so their intersection
  are is just `N`.

  So why are we going through this trouble just to get back to `N`? The reason
  is that we have defined quotients to be an operation on a group and its normal
  subgroups. Notice that `comap (𝒾 (T ⊔ N)) N` does not have the same type as `N`.
  While `N` has type `normal G`, `comap (𝒾 (T ⊔ N)) N` has type `normal (T ⊔ N)`
  as demonstrated by the diagramme above. This is the type we need since we
  can only quotient `T ⊔ N` by one of its normal subgroups.
-/

-- Proving the second isomorphism theorem using the first 

-- `aux_hom` is the natural group homomorphism that maps `t : T` to 
-- `(t : T ⨯ N) : (T ⨯ N) /ₘ comap (𝒾 (T ⨯ N)) N`
def aux_hom (T : subgroup G) (N : normal G) : 
  T →* ↥(T ⨯ N) /ₘ comap (𝒾 (T ⨯ N)) N := (mk _) ∘* (to_prod T N)

@[simp] lemma aux_hom_def {T : subgroup G} {N : normal G} (g) : 
  aux_hom T N g = (mk _) (to_prod T N g) := rfl

-- `aux_hom` has kernel `comap (𝒾 T) N` or equivalently `T ⊓ N`
lemma aux_hom_kernel {T : subgroup G} {N : normal G} : 
  kernel (aux_hom T N) = comap (𝒾 T) N :=
begin
  ext, split; 
    { rw [mem_kernel, aux_hom_def, ←coe_eq_mk, ←coe_one, mk_eq'],
      intro hx, simpa using hx }
end

-- `aux_hom` is a surjective homomorphism
lemma aux_hom_surjective (T : subgroup G) (N : normal G) : 
  surjective $ aux_hom T N :=
begin
  intro y,
  rcases exists_mk y with ⟨g, rfl⟩,
  rcases g with ⟨_, t, ht, n, hn, rfl⟩,
  refine ⟨⟨t, ht⟩, _⟩,
  rw [aux_hom_def, ←coe_eq_mk, mk_eq'],
  simp [group.mul_assoc, show n⁻¹ ∈ N, by exact inv_mem (N : subgroup G) hn]
end

def second_iso_theorem (T : subgroup G) (N : normal G) :
  T /ₘ comap (𝒾 T) N ≅ ↥(T ⨯ N) /ₘ comap (𝒾 (T ⨯ N)) N := 
quotient_kernel_iso_of_surjective' (aux_hom_surjective T N) aux_hom_kernel

-- To state the third isomorphism theorem we need to be able to push forward 
-- (`map`) a normal subgroup along a surjection

def third_iso_theorem (T : normal G) (N : normal G) (h : T.to_subgroup ≤ N) :
  let NmodT : normal (G /ₘ T) := N.nmap is_surjective_mk in
   (G /ₘ T) /ₘ NmodT ≅ G /ₘ N :=
let f : G /ₘ T →* G /ₘ N := (lift (mk N) _ (by { convert h, rw kernel_mk })) in 
iso_comp (subst_iso $ 
    show nmap is_surjective_mk N = f.kernel, by rw [lift_kernel, kernel_mk]) $
  quotient_kernel_iso_of_surjective 
    (by { rw [surjective_iff_max_img, lift_image, ←surjective_iff_max_img],
      exact is_surjective_mk })

-- We would like to define `correspondence N : H ↦ H /ₘ N` so first we need to 
-- show if `H : subgroup G` with `(N : subgroup G) ≤ H`, then `↑N` is a normal 
-- subgroup of `H`

-- I think what I need it a way to make a subgroup from a group, i.e. given `G` 
-- and `H` both groups, if there is a map from `H` to `G`, `f` then there 
-- is a induced subgroup of `G` from `H` using `image f`

/-- `qmap` is a group homomorphism from `H /ₘ N →* G /ₘ N` where `H : subgroup G` 
  and `N : normal G` such that `h ⋆ N ↦ h ⋆ N` -/ 
def qmap (H : subgroup G) (N : normal G) : H /ₘ comap (𝒾 H) N →* G /ₘ N :=
  let φ : H →* G /ₘ N := ⟨λ h, mk N h.1, λ _ _, rfl⟩ in lift φ (comap (𝒾 H) N) $ 
begin
  rintro ⟨x, hx₀⟩ hx,
  show _ ∈ kernel φ,
  rw mem_kernel,
  show mk N x = 1,
  rw [←coe_eq_mk, ←coe_one, mk_eq'],
  change _ ∈ normal.comap (𝒾 H) N at hx,
  simp * at *,
end

@[simp] lemma qmap_eq {H : subgroup G} {N : normal G} (h : H) : 
  qmap H N h = mk N h := rfl

lemma mem_qmap_image {H : subgroup G} {N : normal G} (h) : 
  h ∈ (qmap H N).image ↔ ∃ (g : H /ₘ comap (𝒾 H) N), qmap H N g = h := iff.rfl

lemma injective_qmap {H : subgroup G} {N : normal G} : injective $ qmap H N :=
begin
  intros x y hxy,
  rcases exists_mk x with ⟨x, rfl⟩,
  rcases exists_mk y with ⟨y, rfl⟩,
  change mk N x = mk N y at hxy,
  rw [←coe_eq_mk, ←coe_eq_mk, mk_eq'] at hxy,
  rw [mk_eq', mem_comap],
  exact hxy 
end

def correspondence (N : normal G) : 
  subgroup_ge G N → subgroup_ge (G /ₘ N) ⊥ := λ ⟨H, hH⟩,
subgroup_ge.mk (image $ qmap H N) bot_le

def correspondence_inv (N : normal G) : 
  subgroup_ge (G /ₘ N) ⊥ → subgroup_ge G N := λ ⟨H, hH⟩,
subgroup_ge.mk (subgroup.comap (mk N) H) $
  λ n hn, show mk N n ∈ H, 
  by { convert one_mem H, rw [←mem_kernel, kernel_mk], exact hn }

lemma correspondence_left_inv (N : normal G) : 
  left_inverse (correspondence_inv N) (correspondence N) :=
begin
  rintro ⟨H, hH⟩,
  suffices : comap (mk N) (qmap H N).image = H,
   { simpa [correspondence, correspondence_inv] },
  ext x, split; intro hx,
   { cases hx with x' hx', rcases exists_mk x' with ⟨g, rfl⟩,
     rw [qmap_eq, ←coe_eq_mk, ←coe_eq_mk, mk_eq'] at hx',
     rw ←group.inv_inv x,
     refine inv_mem H _,
     rw [←group.mul_one x⁻¹, ←group.mul_right_inv (g : G), ←group.mul_assoc],
     exact mul_mem H (hH hx') (inv_mem H g.2) },
   { refine ⟨((⟨x, hx⟩ : H) : H /ₘ comap (𝒾 H) N), _⟩,
     rw qmap_eq, refl }
end

lemma correspondence_right_inv (N : normal G) : 
  right_inverse (correspondence_inv N) (correspondence N) :=
begin
  rintro ⟨H, _⟩,
  suffices : (qmap (comap (mk N) H) N).image = H,
    { simpa [correspondence, correspondence_inv] },
  ext x, split; intro hx,
    { rcases hx with ⟨x', rfl⟩,
      rcases exists_mk x' with ⟨⟨g, hg⟩, rfl⟩,
      exact hg },
    { rcases exists_mk x with ⟨g, rfl⟩,
      exact ⟨(mk (comap (𝒾 (comap (mk N) H)) N)) ⟨g, hx⟩, rfl⟩ }
end

def subgroups_of_quotient_equiv (N : normal G) : 
  subgroup_ge G N ≃ subgroup_ge (G /ₘ N) ⊥ := 
{ to_fun := correspondence N,
  inv_fun := correspondence_inv N,
  left_inv := correspondence_left_inv N,
  right_inv := correspondence_right_inv N }

def gc (N : normal G) : galois_connection (subgroups_of_quotient_equiv N).to_fun 
  (subgroups_of_quotient_equiv N).inv_fun := 
begin
  intros A B,
  cases A with A hA,
  cases B with B _,
  split; intros h a ha,
    { exact h ⟨((⟨a, ha⟩ : A) : _), rfl⟩ },
    { rcases ha with ⟨x, rfl⟩,
      rcases exists_mk x with ⟨⟨g, hg⟩, rfl⟩,
      exact h hg }
end

-- ↓ This turns out to be useless since gc + equiv = order_iso ⇒ gi...
def gi (N : normal G) : galois_insertion (subgroups_of_quotient_equiv N).to_fun 
  (subgroups_of_quotient_equiv N).inv_fun := 
{ choice := λ x _, (subgroups_of_quotient_equiv N).to_fun x,
  gc := gc N,
  le_l_u := λ x, by { rw (subgroups_of_quotient_equiv N).right_inv, exact le_refl _ },
  choice_eq := λ _ _, rfl }

/-- The subgroups of `G` greater than some `N : normal G` is order isomorphic to 
  the subgroups of `G /ₘ N` greater than `⊥` -/
def subgroups_of_quotient_order_iso (N : normal G) : 
  let A := subgroup_ge G N in 
  let B := subgroup_ge (G /ₘ N) ⊥ in
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) :=
lattice.order_iso_of_equiv_gi (subgroups_of_quotient_equiv N) (gc N)

/-- The subgroups of `G` greater than some `N : normal G` is order isomorphic to 
  the subgroups of `G /ₘ N` -/
def subgroups_of_quotient_order_iso' (N : normal G) : 
  let A := subgroup_ge G N in 
  let B := subgroup (G /ₘ N) in
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) :=
order_iso.trans (subgroups_of_quotient_order_iso N) $
  order_iso.symm ge.subgroup_ge_bot_order_iso

-- We would like a lemma that states : Given `G` groups, `N : normal G`, the 
-- preimage of `H : subgroup G /ₘ N` under the natural map from `G` to `G /ₘ N`
-- is a subgroup of `G` with order `|H||N|`.

def quotient.comap (N : normal G) (H : subgroup (G /ₘ N)) : subgroup G := 
  subgroup.comap (mk N) H

lemma quotient.comap_le (N : normal G) (H : subgroup (G /ₘ N)) : 
  (N : set G) ⊆ quotient.comap N H := λ n hn, 
show _ ∈ H, by { convert one_mem H, rw [← mem_kernel, kernel_mk], exact hn }

-- The way to think about this is that `mk⁻¹ H` is the new group with `N` its 
-- normal subgroup. Now, by `kernel_mk` we have `kernel mk = N` so by the 
-- first isomorphism theorem `mk⁻¹ H /ₘ N ≅ H`

lemma quotient.comap_iso (N : normal G) (H : subgroup (G /ₘ N)) :
  quotient.comap N H /ₘ comap (𝒾 $ quotient.comap N H) N ≅ H :=
  let f : quotient.comap N H →* H :=
    { to_fun := λ x, ⟨mk N x.1, x.2⟩,
      map_mul' := λ _ _, rfl } in
  quotient_kernel_iso_of_surjective' (begin
    rintro ⟨y, hy⟩,
    rcases exists_mk y with ⟨g, rfl⟩,
    use [g, hy], refl
  end : surjective f)
  begin
    ext x,
    rw [mem_kernel, mem_comap],
    unfold coe_fn has_coe_to_fun.coe,
    simp only [to_fun_eq_coe, subtype.val_eq_coe],
    cases x with x hx,
    change _ ↔ x ∈ N,
    conv_rhs begin rw ←@kernel_mk _ _ N, end,
    rw mem_kernel,
    show _ = (⟨(1 : G /ₘ N), _⟩ : H) ↔ _, simp
  end

lemma quotient.comap_card_eq [fintype G] (N : normal G) (H : subgroup (G /ₘ N)) : 
  fincard (quotient.comap N H) = 
  fincard (normal.comap (𝒾 $ quotient.comap N H) N) * fincard H :=
begin
  rw [fincard.of_equiv (mul_equiv_of_iso (iso_symm (quotient.comap_iso N H))).to_equiv,
     ← lagrange.card_quotient_eq_mul]
end

end quotient

end mygroup

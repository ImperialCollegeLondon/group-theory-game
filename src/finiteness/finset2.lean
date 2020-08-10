-- bundled noncomputable finite sets
import tactic

import data.set.finite

namespace fintype

universes u v

@[ext] def ext {X : Type u} (a : fintype X) (b : fintype X) :
a = b := subsingleton.elim a b

def equiv_congr {X : Type u} {Y : Type v} (e : X ≃ Y) :
  fintype X ≃ fintype Y :=
{ to_fun := λ fX, @fintype.of_equiv Y X fX e,
  inv_fun := λ fY, @fintype.of_equiv X Y fY e.symm,
  left_inv := begin
    intro h,
    ext,
  end,
  right_inv := begin
    intro h,
    ext,
  end }

end fintype

namespace nonempty

universes u v

lemma of_nonempty_equiv {X : Type u} {Y : Type v} (f : X → Y) :
  nonempty X → nonempty Y :=
begin
  exact map f,
end

end nonempty

open_locale classical

universe u

variable {X : Type u}

open set

def finset2 (X : Type u) := {S : set X // finite S}

namespace finset2

-- finset2 is the same as finset

-- Group theory Sylow theorems : proposal that we do all counting
-- with finset2

-- proofs can certainly be golfed

noncomputable def equiv_finset (X : Type*) : finset2 X ≃ (finset X) :=
{ to_fun := λ T, T.2.to_finset,
  inv_fun := λ F, ⟨↑F, finite_mem_finset F⟩, 
  left_inv := begin
    intro T,
    cases T with S h,
    ext x,
    apply finite.mem_to_finset,
  end,
  right_inv := begin
    intro F,
    dsimp,
    ext x,
    set S : set X := ↑F,
    rw ←(@finset.mem_coe _ _ F),
    rw finite.mem_to_finset
  end }

noncomputable def card (F : finset2 X) : ℕ :=
((finset2.equiv_finset X).to_fun F).card

-- now every theorem for finset I want for finset2

-- maybe some tactic can get them for me

end finset2

/-! # Relation to fintype -/

def equiv.univ (X : Type u) :
X ≃ (univ : set X) :=
{ to_fun := λ x,  ⟨x, mem_univ x⟩,
  inv_fun := λ cx, cx.1,
  left_inv := by intro x; refl,
  right_inv := by intro cx; cases cx; refl }

universe v

-- two concepts of finiteness are EQUIVALENT
theorem nonempty_fintype_iff_finite_univ : nonempty (fintype X) ↔ finite (univ : set X) :=
begin
  split,
  { unfold finite,
    intro h,
    exact nonempty.map (fintype.equiv_congr (equiv.univ X)) h
  },
  { intro h,
    cases h,
    cases h with S hS,
    let elems : finset X := finset.map (equiv.to_embedding (equiv.univ X).symm) S,
    use { elems := elems, complete := begin
      intro x,
      change x ∈ finset.map (equiv.univ X).symm.to_embedding S,
      rw finset.mem_map,
      use ⟨x, mem_univ x⟩,
      split,
        apply hS,
      refl,
    end},
  }
end

--noncomputable def set.fincard {X : Type u} (S : set X) : ℕ :=
--if h : S.finite then (⟨S, h⟩ : finset2 X).card else 37

--noncomputable def fincard (X : Type*) : ℕ :=
--if h : nonempty (fintype X) then @fintype.card X (classical.choice h) else 0

-- I proved fincard.prod


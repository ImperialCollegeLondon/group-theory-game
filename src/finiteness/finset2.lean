#exit
-- bundled noncomputable finite sets
import tactic

import data.set.finite

def subsingleton.mk_equiv {α β} [subsingleton α] [subsingleton β]
  (f : α → β) (g : β → α) : α ≃ β :=
⟨f, g, λ _, by cc, λ _, by cc⟩

namespace fintype

universes u v

@[ext] def ext {X : Type u} (a : fintype X) (b : fintype X) :
a = b := subsingleton.elim a b

def equiv_congr {X Y} (e : X ≃ Y) : fintype X ≃ fintype Y :=
subsingleton.mk_equiv (λ fX, @fintype.of_equiv Y X fX e) (λ fY, @fintype.of_equiv X Y fY e.symm)

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

-- Don't know if I need it
-- should prove it's equivalent to Avigad's version

-- noncomputable def set.fincard {X : Type u} (S : set X) : ℕ :=
-- if h : S.finite then finset2.card (⟨S, h⟩ : finset2 X) else 37


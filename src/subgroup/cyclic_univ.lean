import subgroup.cyclic
import orbit.orbit_stabilizer

namespace mygroup

variables {G : Type} [group G] {S : Type}

def action.to_equiv (μ : laction G S) (g : G) : S ≃ S :=
{ to_fun := λ s, g •[μ] s,
  inv_fun := λ t, g⁻¹ •[μ] t,
  left_inv := λ s, begin simp, rw laction.map_assoc, simp end,
  right_inv := λ s, begin simp, rw laction.map_assoc, simp end }

def action_eq_hom : laction G S ≃ (G →* (S ≃ S)) :=
{ to_fun := λ μ,
  { to_fun := λ g, action.to_equiv μ g,
    map_mul' := begin
      intros x y,
      ext s,
      show (x * y) •[μ] s = x •[μ] (y •[μ] s),
      exact (laction.map_assoc x y s).symm,  
    end
     },
  inv_fun := λ φ, 
  { to_fun := λ g s, φ g s,
    map_one' := by {rw φ.map_one, intros, refl},
    map_assoc' := by {intros g h s, simp} },
  left_inv := λ μ, begin
    ext g s,
    simp,
    refl
  end,
  right_inv := λ φ, begin
    ext g s,
    refl,
  end }

end mygroup



import subgroup.theorems data.quot

namespace mygroup

namespace quotient

#check quotient -- quotient takes a setoid (a type equiped with an equivalence 
-- relation) and gives us a sort

open subgroup lagrange

-- We will create the quotient subgroup by defining an equivalence relation on 
-- the group G where ∀ g h : G, rel g h ↔ g • H = h • H where H ≤ G

-- See: https://courses.maths.ox.ac.uk/node/view_material/43836 p.57

variables {G : Type} [group G]

def rel (H : subgroup G) (g h : G) : Prop := g • H = h • H

def rel_setoid (H : subgroup G) : setoid G := 
{ r := rel H,
  iseqv := 
  begin
    refine ⟨by tauto, λ _ _ hxy, hxy.symm, _⟩,
      { intros _ _ _ hxy hyz,
        unfold rel at *,
        rw [hxy, hyz] }
  end }

def group_quotient (G : Type) [group G] (H : subgroup G) := 
  quotient $ rel_setoid H
notation G ` / ` H := group_quotient G H

-- Now we will make group_quotient into a group whenever its a group quotient on 
-- a normal subgroup

variables {H : subgroup G}

instance : has_coe G (G / H) := ⟨λ g, quotient.mk' g⟩

lemma eq {g h : G} : (g : G / H) = h ↔ h⁻¹ * g ∈ H := 
begin
  -- convert lcoset_eq,
  sorry
end

instance {H : subgroup G} : has_mul $ G / H := sorry
instance {H : subgroup G} : has_one $ G / H := sorry
instance {H : subgroup G} : has_inv $ G / H := sorry

instance {H : normal G} : group $ G / H := 
{ mul := (*), one := (1), inv := has_inv.inv,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_left_inv := sorry }

end quotient

end mygroup
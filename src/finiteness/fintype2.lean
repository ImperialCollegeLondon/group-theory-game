import finiteness.finset2

universe u

open_locale classical

def fintype2 (X : Type u) : Prop := nonempty (fintype X)

attribute [class] fintype2

namespace fintype2

lemma obvious (X : Type u) : nonempty X ↔ ∃ (x : X), true :=
begin
  exact exists_true_iff_nonempty.symm,
end

instance set {X : Type u} [fintype2 X] (s : set X) : fintype2 ↥s :=
begin
  unfold fintype2 at *,
  apply nonempty.map _ _inst_1,
  intro useless,
  resetI, -- puts all typeclasses in the local context into the inference system
  exact set_fintype s,
end

end fintype2


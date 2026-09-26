module

public import Foundation.ProvabilityLogic.Kripke.Basic

/-!
# Overwriting the valuation of a Kripke model
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Formula Model.World

namespace Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {V : κ → α → Prop}

def overwrite (M : Model κ α) (V : M.World → α → Prop) : Model κ α := ⟨M.Rel', V⟩

instance [M.IsFiniteGL] : (M.overwrite V).IsFiniteGL where
  trans := IsTrans.trans (r := M.Rel)
  irrefl := Std.Irrefl.irrefl (r := M.Rel)
  finite := IsFiniteGL.finite (M := M)

lemma forces_overwrite_subst {s : Substitution α α} {x : M.World} {A : Formula α} :
    x ⊩[M.overwrite fun y a ↦ y ⊩[M] s a] A ↔ x ⊩[M] A⟦s⟧ := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp _ _ ihA ihB => exact imp_congr ihA ihB;
  | box _ ih => exact forall_congr' fun _ ↦ imp_congr_right fun _ ↦ ih;

end Model

end FFL.ProvabilityLogic.Kripke

end

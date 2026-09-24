module

public import Foundation.ProvabilityLogic.Logic
public import Foundation.ProvabilityLogic.Kripke.Basic

/-!
# Kripke soundness of normal logics
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke Kripke.Model Kripke.Model.World

namespace Logic.normalOf

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {𝔸 : Set (Formula α)} {A : Formula α}

theorem sound (h𝔸 : ∀ A ∈ 𝔸, M ⊧ A) (h : normalOf 𝔸 ⊢ A) : M ⊧ A := by
  intro x;
  induction h generalizing x with
  | axm hA => exact h𝔸 _ hA x;
  | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
  | nec _ ih => exact fun y _ ↦ ih y;
  | axiomK => exact fun h₁ h₂ y Rxy ↦ h₁ y Rxy (h₂ y Rxy);
  | _ => simp only [Axioms.Verum, Axioms.ImplyK, Axioms.ImplyS, Axioms.AndElim₁, Axioms.AndElim₂,
      Axioms.AndInst, Axioms.OrInst₁, Axioms.OrInst₂, Axioms.OrElim, Axioms.DNE]; grind;

end Logic.normalOf

end FFL.ProvabilityLogic

end

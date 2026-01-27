module

public import Foundation.Modal.Kripke.Logic.Grz.Completeness
public import Foundation.Modal.Kripke.Logic.S4
public import Foundation.Modal.Kripke.AxiomH
public import Foundation.Modal.Kripke.Filtration
public import Foundation.Modal.Kripke.Rooted

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke


namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4H (F : Frame) extends F.IsReflexive, F.IsTransitive, F.IsDetourFree where
protected class Frame.IsFiniteS4H (F : Frame) extends F.IsFinite, F.IsS4H where

protected abbrev FrameClass.S4H : FrameClass := { F | F.IsS4H }
protected abbrev FrameClass.finite_S4H : FrameClass := { F | F.IsFiniteS4H }

instance [F.IsFiniteS4H] : F.IsFiniteGrz where

end Kripke


namespace S4H

instance : Sound (Modal.S4H) FrameClass.S4H := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomH_of_isDetourFree;

instance : Entailment.Consistent (Modal.S4H) := consistent_of_sound_frameclass FrameClass.S4H $ by
  use whitepoint;
  constructor;

instance : Canonical (Modal.S4H) FrameClass.S4H := ⟨by constructor⟩

instance : Complete (Modal.S4H) FrameClass.S4H := inferInstance

instance : Complete Modal.S4H FrameClass.finite_S4H := by sorry

end S4H


instance : Modal.Grz ⪱ Modal.S4H := by
  constructor;
  . apply weakerThan_of_subset_frameClass (FrameClass.finite_Grz) (FrameClass.finite_S4H)
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.H (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.finite_Grz)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x ≤ y⟩, λ w a => w ≠ 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact {}
      . suffices ∃ x : M, (0 : M) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 ∧ x = 1 by
          simp [Semantics.Models, Satisfies, M];
          grind;
        use 1;
        constructor;
        . tauto;
        . use 2;
          grind;


end LO.Modal
end

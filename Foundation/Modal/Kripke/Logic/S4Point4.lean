module
import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.AxiomPoint4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point4 (F : Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesSobocinskiCondition

protected abbrev FrameClass.S4Point4 : FrameClass := { F | F.IsS4Point4 }

instance [F.IsS4Point4] : F.IsS4Point3 where

end Kripke


namespace Modal.S4Point4.Kripke

instance : Sound Modal.S4Point4 FrameClass.S4Point4 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance : Entailment.Consistent Modal.S4Point4 :=
  consistent_of_sound_frameclass FrameClass.S4Point4 $ by
    use whitepoint;
    constructor;

instance : Canonical Modal.S4Point4 FrameClass.S4Point4 := ⟨by constructor⟩

instance : Complete Modal.S4Point4 FrameClass.S4Point4 := inferInstance


instance : Modal.S4Point3 ⪱ Modal.S4Point4 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.S4Point3) (FrameClass.S4Point4);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Point4 (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4Point3)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x ≤ y⟩,
        λ w a => w ≠ 1
      ⟩;
      use M, 0;
      constructor;
      . exact {};
      . suffices ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M.World) ≺ 1 by
          simpa [Semantics.Models, Satisfies, M];
        use 2;
        omega;

end Modal.S4Point4.Kripke


end LO.Modal

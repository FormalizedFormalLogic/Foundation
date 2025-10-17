import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.K4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

class Frame.IsK4Point2 (F : Kripke.Frame) extends F.IsTransitive, F.IsPiecewiseConvergent where

abbrev FrameClass.K4Point2 : FrameClass := { F | F.IsK4Point2 }

end Kripke

instance : Sound (Modal.K4Point2) Kripke.FrameClass.K4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint2_of_weakConfluent;

instance : Entailment.Consistent Modal.K4Point2 :=
  consistent_of_sound_frameclass Kripke.FrameClass.K4Point2 $ by
    use whitepoint;
    constructor;

instance : Canonical (Modal.K4Point2) Kripke.FrameClass.K4Point2 :=  ⟨by constructor⟩

instance : Complete (Modal.K4Point2) Kripke.FrameClass.K4Point2 := inferInstance

instance : Modal.K4 ⪱ Modal.K4Point2 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.WeakPoint2 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint2!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x = 0⟩,
        λ w a => if a = 0 then True else w = 0
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact { trans := by omega };
      . suffices ∃ (x : M.World), (∀ y, ¬x ≺ y) ∧ x ≠ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor;
        . omega;
        . trivial;

end LO.Modal

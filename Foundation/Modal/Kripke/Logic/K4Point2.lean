import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

class Frame.IsK4Point2 (F : Kripke.Frame) extends F.IsTransitive, F.IsPiecewiseConvergent where

abbrev FrameClass.K4Point2 : FrameClass := { F | F.IsK4Point2 }

end Kripke


namespace Hilbert.K4Point2.Kripke

instance : Sound (Hilbert.K4Point2) Kripke.FrameClass.K4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint2_of_weakConfluent;

instance : Entailment.Consistent Hilbert.K4Point2 :=
  consistent_of_sound_frameclass Kripke.FrameClass.K4Point2 $ by
    use whitepoint;
    constructor;

instance : Canonical (Hilbert.K4Point2) Kripke.FrameClass.K4Point2 :=  ⟨by constructor⟩

instance : Complete (Hilbert.K4Point2) Kripke.FrameClass.K4Point2 := inferInstance

lemma K4Point2 : Modal.K4Point2 = FrameClass.K4Point2.logic := eq_hilbert_logic_frameClass_logic

instance : Hilbert.K4 ⪱ Hilbert.K4Point2 := by
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

end Hilbert.K4Point2.Kripke

end LO.Modal

import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsK4Point3 (F : Kripke.Frame) extends F.IsTransitive, F.IsPiecewiseConnected

abbrev FrameClass.IsK4Point3 : FrameClass := { F | F.IsK4Point3 }

end Kripke


namespace Logic.K4Point3.Kripke

instance sound : Sound Logic.K4Point3 FrameClass.IsK4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint3_of_weakConnected;

instance consistent : Entailment.Consistent Logic.K4Point3 :=
  consistent_of_sound_frameclass FrameClass.IsK4Point3 $ by
    use whitepoint;
    constructor;

instance canonical : Canonical Logic.K4Point3 FrameClass.IsK4Point3 :=  ⟨by constructor⟩

instance complete : Complete Logic.K4Point3 FrameClass.IsK4Point3 := inferInstance

lemma trans_weakConnected : Logic.K4Point3 = FrameClass.IsK4Point3.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K4 ⪱ Logic.K4Point3 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K4Point3 ⊢! φ ∧ ¬FrameClass.K4 ⊧ φ by simpa [K4.Kripke.trans];
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∧ y ≠ 0⟩,
        λ w a => if a = 0 then w = 1 else w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact { trans := by omega }
      . suffices
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 1 ∧ (∀ y, x ≺ y → y = 1) ∧ ¬x = 2 ∧
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 2 ∧ (∀ z : M.World, x ≺ z → z = 2) ∧ x ≠ 1
          by simpa [M, Semantics.Realize, Satisfies];
        refine ⟨1, ?_, rfl, ?_, ?_, 2, ?_, rfl, ?_, ?_⟩;
        . trivial;
        . omega;
        . trivial;
        . omega;
        . trivial;
        . trivial;

end Logic.K4Point3.Kripke

end LO.Modal

import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K4

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.trans_weakConfluent : FrameClass := { F | F.IsTransitive ∧ F.IsPiecewiseConvergent }

namespace Hilbert.K4Point2.Kripke

instance sound : Sound (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint2_of_weakConfluent;

instance consistent : Entailment.Consistent (Hilbert.K4Point2) :=
  consistent_of_sound_frameclass FrameClass.trans_weakConfluent $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    . infer_instance;
    . infer_instance;

instance canonical : Canonical (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := inferInstance

end Hilbert.K4Point2.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma K4Point2.Kripke.trans_weakConfluent : Logic.K4Point2 = FrameClass.trans_weakConfluent.logic := eq_hilbert_logic_frameClass_logic

theorem K4Point2.proper_extension_of_K4 : Logic.K4 ⊂ Logic.K4Point2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Point2 ⊢! φ ∧ ¬Kripke.FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.WeakPoint2 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
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

end Logic

end LO.Modal

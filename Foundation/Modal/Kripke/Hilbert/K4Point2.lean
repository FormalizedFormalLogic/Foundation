import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.trans_weakConfluent : FrameClass := { F | IsTrans _ F ∧ IsWeakConfluent _ F }

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

lemma Logic.K4Point2.Kripke.trans_weakConfluent : Logic.K4Point2 = FrameClass.trans_weakConfluent.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

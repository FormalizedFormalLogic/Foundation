import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.trans_weakConnected : FrameClass := { F | IsTrans _ F ∧ IsWeakConnected _ F }

namespace Hilbert.K4Point3.Kripke

instance sound : Sound (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_WeakPoint3_of_weakConnected;

instance consistent : Entailment.Consistent (Hilbert.K4Point3) :=
  consistent_of_sound_frameclass FrameClass.trans_weakConnected $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    constructor;
    . infer_instance;
    . infer_instance;

instance canonical : Canonical (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := inferInstance

end Hilbert.K4Point3.Kripke

end LO.Modal

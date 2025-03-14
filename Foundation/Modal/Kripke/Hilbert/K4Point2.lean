import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.trans_weakConfluent : FrameClass := { F | Transitive F ∧ WeakConfluent F }

namespace Kripke.FrameClass.trans_weakConfluent

@[simp]
protected lemma nonempty : Kripke.FrameClass.trans_weakConfluent.Nonempty := by
  use whitepoint;
  simp [Transitive, WeakConfluent];

lemma validates_HilbertK4Point2 : Kripke.FrameClass.trans_weakConfluent.Validates Hilbert.K4Point2.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_trans, F_wc⟩ φ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . apply weakConfluent_of_validate_WeakPoint2 F_wc;

end Kripke.FrameClass.trans_weakConfluent


namespace Hilbert.K4Point2.Kripke

instance sound : Sound (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent :=
  instSound_of_validates_axioms FrameClass.trans_weakConfluent.validates_HilbertK4Point2

instance consistent : Entailment.Consistent (Hilbert.K4Point2) :=
  consistent_of_sound_frameclass FrameClass.trans_weakConfluent (by simp)

instance canonical : Canonical (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := ⟨Canonical.transitive, Canonical.weakConfluent⟩

instance complete : Complete (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := inferInstance

end Hilbert.K4Point2.Kripke

end LO.Modal

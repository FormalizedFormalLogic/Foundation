import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.trans_weakConnected : FrameClass := { F | Transitive F ∧ WeakConnected F }

namespace Kripke.FrameClass.trans_weakConnected

@[simp]
protected lemma nonempty : Kripke.FrameClass.trans_weakConnected.Nonempty := by
  use whitepoint;
  simp [Transitive, WeakConnected];

lemma validates_HilbertK4Point3 : Kripke.FrameClass.trans_weakConnected.Validates Hilbert.K4Point3.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . apply weakConnected_of_validate_WeakPoint3 $ by assumption;;

end Kripke.FrameClass.trans_weakConnected


namespace Hilbert.K4Point3

instance Kripke.sound : Sound (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected :=
  instSound_of_validates_axioms FrameClass.trans_weakConnected.validates_HilbertK4Point3

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Point3) :=
  consistent_of_sound_frameclass FrameClass.trans_weakConnected (by simp)

instance Kripke.canonical : Canonical (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := ⟨Canonical.transitive, Canonical.weakConnected⟩

instance Kripke.complete : Complete (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := inferInstance

end Hilbert.K4Point3

end LO.Modal

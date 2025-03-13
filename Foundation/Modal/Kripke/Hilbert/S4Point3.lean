import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomPoint3

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.connected_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

namespace Kripke.FrameClass.connected_preorder

@[simp]
protected lemma nonempty : Kripke.FrameClass.connected_preorder.Nonempty := by
  use whitepoint;
  simp [Reflexive, Transitive, Connected];

lemma validates_HilbertS4Point3 : Kripke.FrameClass.connected_preorder.Validates Hilbert.S4Point3.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive $ by assumption
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . exact validate_AxiomPoint3_of_connected $ by assumption;

end Kripke.FrameClass.connected_preorder


namespace Hilbert.S4Point3.Kripke

instance sound : Sound (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder :=
  instSound_of_validates_axioms FrameClass.connected_preorder.validates_HilbertS4Point3

instance consistent : Entailment.Consistent (Hilbert.S4Point3) :=
  consistent_of_sound_frameclass FrameClass.connected_preorder (by simp)

instance canonical : Canonical (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder :=
  ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.connected⟩⟩

instance complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := inferInstance

end Hilbert.S4Point3.Kripke


end LO.Modal

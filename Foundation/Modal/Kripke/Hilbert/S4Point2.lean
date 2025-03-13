import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.confluent_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F  }

namespace Kripke.FrameClass.confluent_preorder

lemma isMultiGeachean : FrameClass.confluent_preorder = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.confluent_preorder.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertS4Point2 : Kripke.FrameClass.confluent_preorder.Validates Hilbert.S4Point2.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_refl, F_trans, F_conn⟩ φ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive F_refl;
  . exact validate_AxiomFour_of_transitive F_trans;
  . exact validate_AxiomPoint2_of_confluent F_conn;

end Kripke.FrameClass.confluent_preorder


namespace Hilbert.S4Point2

instance Kripke.sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder :=
  instSound_of_validates_axioms FrameClass.confluent_preorder.validates_HilbertS4Point2

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4Point2) :=
  consistent_of_sound_frameclass FrameClass.confluent_preorder (by simp)

instance Kripke.canonical : Canonical (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.confluent⟩⟩

instance Kripke.complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := inferInstance

end Hilbert.S4Point2

end LO.Modal

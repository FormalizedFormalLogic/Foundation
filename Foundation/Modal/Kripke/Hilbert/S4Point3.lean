import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomPoint3
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.connected_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }
abbrev Kripke.FrameClass.finite_connected_preorder : FrameClass := { F | F.IsFinite ∧ Reflexive F ∧ Transitive F ∧ Connected F }

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


section FFP

open
  finestFilterationTransitiveClosureModel
  Relation
instance finite_complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.finite_connected_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨F_refl, F_trans, F_conn⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  have RM_refl : Reflexive RM.Rel := Frame.pointGenerate.rel_refl F_refl;
  have RM_trans : Transitive RM.Rel := Frame.pointGenerate.rel_trans F_trans;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel RM (φ.subformulas);
  apply filteration FRM (finestFilterationTransitiveClosureModel.filterOf RM_trans) (by aesop) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . exact reflexive_of_transitive_reflexive RM_trans RM_refl;
  . exact finestFilterationTransitiveClosureModel.transitive;
  . rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [or_self]; apply Relation.TransGen.single; tauto;
    . replace Rrz := TransGen.unwrap F_trans Rrz;
      left;
      apply Relation.TransGen.single $ by tauto;
    . replace Rry := TransGen.unwrap F_trans Rry;
      right;
      apply Relation.TransGen.single $ by tauto;
    . replace Rry := TransGen.unwrap F_trans Rry;
      replace Rrz := TransGen.unwrap F_trans Rrz;
      rcases F_conn ⟨Rry, Rrz⟩ with (Ryz | Rrw);
      . left; apply Relation.TransGen.single; tauto;
      . right; apply Relation.TransGen.single; tauto;
⟩

end FFP

end Hilbert.S4Point3.Kripke


end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.confluent_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F  }
abbrev Kripke.FrameClass.finite_confluent_preorder : FrameClass := { F | F.IsFinite ∧ Reflexive F ∧ Transitive F ∧ Confluent F  }

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


namespace Hilbert.S4Point2.Kripke

instance sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder :=
  instSound_of_validates_axioms FrameClass.confluent_preorder.validates_HilbertS4Point2

instance consistent : Entailment.Consistent (Hilbert.S4Point2) :=
  consistent_of_sound_frameclass FrameClass.confluent_preorder (by simp)

instance canonical : Canonical (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.confluent⟩⟩

instance complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := inferInstance


section FFP

open
  finestFilterationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨F_refl, F_trans, F_con⟩ V r;
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
    . simp only [and_self];
      use ⟦⟨z, by tauto⟩⟧;
      apply Relation.TransGen.single; tauto;
    . use ⟦⟨z, by tauto⟩⟧;
      constructor;
      . replace Rrz := TransGen.unwrap F_trans Rrz;
        apply Relation.TransGen.single $ by tauto;
      . apply Relation.TransGen.single $ by tauto;
    . use ⟦⟨y, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single $ by tauto;
      . replace Rry := TransGen.unwrap F_trans Rry;
        apply Relation.TransGen.single $ by tauto;
    . replace Rry := TransGen.unwrap F_trans Rry;
      replace Rrz := TransGen.unwrap F_trans Rrz;
      obtain ⟨u, Ruy, Ruz⟩ := F_con ⟨Rry, Rrz⟩;
      use ⟦⟨u, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single $ by tauto;
      . apply Relation.TransGen.single $ by tauto;
⟩

end FFP

end Hilbert.S4Point2.Kripke

end LO.Modal

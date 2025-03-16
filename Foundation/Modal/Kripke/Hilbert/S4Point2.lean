import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.Filteration
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.confluent_preorder : FrameClass := { F | IsPreorder _ F ∧ IsConfluent _ F  }
abbrev Kripke.FrameClass.finite_confluent_preorder : FrameClass := { F | Finite F.World ∧ IsPreorder _ F ∧ IsConfluent _ F }

namespace Hilbert.S4Point2.Kripke

instance sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent (Hilbert.S4Point2) :=
  consistent_of_sound_frameclass FrameClass.confluent_preorder $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ?_⟩;
  . constructor;
  . infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := inferInstance


section FFP

open
  finestFilterationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨_, _⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  -- have RM_refl : Reflexive RM.Rel := Frame.pointGenerate.rel_refl F_refl;
  -- have RM_trans : IsTrans _ RM.Rel := inferInstance;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel (M↾r) (φ.subformulas);
  apply filteration FRM (finestFilterationTransitiveClosureModel.filterOf) (by aesop) |>.mpr;
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

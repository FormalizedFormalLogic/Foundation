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

instance finite_sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance finite_complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨_, _⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel (M↾r) (φ.subformulas);
  apply filteration FRM (finestFilterationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTrans)) (by subformula) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . exact finestFilterationTransitiveClosureModel.isPreorder (preorder := Frame.pointGenerate.isPreorder);
  . apply isConfluent_iff _ _ |>.mpr;
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [and_self];
      use ⟦⟨z, by tauto⟩⟧;
      apply Relation.TransGen.single;
      suffices z ≺ z by tauto;
      apply IsRefl.refl;
    . use ⟦⟨z, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single;
        suffices y ≺ z by tauto;
        exact TransGen.unwrap Rrz;
      . apply Relation.TransGen.single;
        suffices z ≺ z by tauto;
        apply IsRefl.refl ;
    . use ⟦⟨y, by tauto⟩⟧;
      constructor;
      . apply Relation.TransGen.single;
        suffices y ≺ y by tauto;
        apply IsRefl.refl;
      . apply Relation.TransGen.single;
        suffices z ≺ y by tauto;
        exact TransGen.unwrap Rry;
    . replace Rry := TransGen.unwrap Rry;
      replace Rrz := TransGen.unwrap Rrz;
      obtain ⟨u, Ruy, Ruz⟩ := IsConfluent.confluent ⟨Rry, Rrz⟩;
      use ⟦⟨u, by
        right;
        apply Relation.TransGen.single;
        exact IsTrans.trans _ _ _ Rry Ruy;
      ⟩⟧;
      constructor;
      . exact Relation.TransGen.single $ by tauto;
      . exact Relation.TransGen.single $ by tauto;
⟩

end FFP

end Hilbert.S4Point2.Kripke

end LO.Modal

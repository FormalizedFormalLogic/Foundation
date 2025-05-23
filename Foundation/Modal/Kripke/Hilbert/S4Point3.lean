import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomPoint3
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.connected_preorder : FrameClass := { F | IsPreorder _ F ∧ IsConnected _ F }
abbrev Kripke.FrameClass.finite_connected_preorder : FrameClass := { F | F.IsFinite ∧ IsPreorder _ F ∧ IsConnected _ F }

/-
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
-/

namespace Hilbert.S4Point3.Kripke

instance sound : Sound (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint3_of_connected;

instance consistent : Entailment.Consistent (Hilbert.S4Point3) :=
  consistent_of_sound_frameclass FrameClass.connected_preorder $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := inferInstance


section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_sound : Sound (Hilbert.S4Point3) Kripke.FrameClass.finite_connected_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint3_of_connected;

instance finite_complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.finite_connected_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨_, _⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTrans)) (by subformula) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_, ?_⟩;
  . apply Frame.isFinite_iff _ |>.mpr
    apply FilterEqvQuotient.finite;
    simp;
  . exact finestFiltrationTransitiveClosureModel.isPreorder (preorder := Frame.pointGenerate.isPreorder);
  . apply isConnected_iff _ _ |>.mpr;
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [or_self];
      apply Relation.TransGen.single;
      suffices z ≺ z by tauto;
      apply IsRefl.refl;
    . left;
      apply Relation.TransGen.single;
      suffices y ≺ z by tauto;
      exact Rrz.unwrap;
    . right;
      apply Relation.TransGen.single;
      suffices z ≺ y by tauto;
      exact Rry.unwrap;
    . replace Rry := Rry.unwrap;
      replace Rrz := Rrz.unwrap;
      rcases IsConnected.connected ⟨Rry, Rrz⟩ with (Ryz | Rrw);
      . left;
        apply Relation.TransGen.single;
        tauto;
      . right;
        apply Relation.TransGen.single;
        tauto;
⟩

end FFP

end Hilbert.S4Point3.Kripke


end LO.Modal

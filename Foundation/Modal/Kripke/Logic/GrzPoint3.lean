import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.Logic.S4Point3

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke


open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

abbrev FrameClass.finite_connected_partial_order : FrameClass := { F | F.IsFinite ∧ IsPartialOrder _ F.Rel ∧ IsConnected _ F.Rel  }

end Kripke


namespace Hilbert.GrzPoint3.Kripke

instance finite_sound : Sound (Hilbert.GrzPoint3) FrameClass.finite_connected_partial_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_AxiomPoint3_of_connected;

instance consistent : Entailment.Consistent (Hilbert.GrzPoint3) :=
  consistent_of_sound_frameclass FrameClass.finite_connected_partial_order $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance finite_complete : Complete (Hilbert.GrzPoint3) (FrameClass.finite_connected_partial_order) :=
  Kripke.Grz.complete_of_mem_miniCanonicalFrame FrameClass.finite_connected_partial_order $ by
    sorry;
    /-
    intro φ;
    refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm, ?_⟩;
    intro x y z ⟨⟨Rxy₁, Rxy₂⟩, ⟨Rxz₁, Rxz₂⟩⟩;
    apply or_iff_not_imp_left.mpr;
    intro nRyz;
    rcases (not_and_or.mp nRyz) with (nRyz | nRyz);
    . push_neg at nRyz;
      obtain ⟨ψ, hψ, ⟨hψy, hψz⟩⟩ := nRyz;
      constructor;
      . intro ξ hξ₁ hξ₂;
        apply Rxy₁;
        . exact hξ₁;
        . sorry;
      . intro hyz;
        have exy := Rxy₂ ?_;
        have exz := Rxz₂ ?_;
        tauto;
        . subst exy;
          intro ξ hξ hξz;
          sorry;
        . intro ξ hξ hξy;
          sorry;
    . push_neg at nRyz;
      replace ⟨nRyz₁, nRyz₂⟩ := nRyz;
      constructor;
      . sorry;
      . sorry;
    -/

end Hilbert.GrzPoint3.Kripke

lemma Logic.GrzPoint3.Kripke.finite_connected_partial_order : Logic.GrzPoint3 = FrameClass.finite_connected_partial_order.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

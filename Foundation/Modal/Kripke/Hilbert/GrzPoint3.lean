import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Point3

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

abbrev FrameClass.finite_connected_partial_order : FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel ∧ Connected F.Rel }

namespace FrameClass.finite_connected_partial_order

@[simp]
lemma nonempty : FrameClass.finite_connected_partial_order.Nonempty := by
  use whitepoint;
  simp [Reflexive, Transitive, AntiSymmetric, Connected];
  infer_instance;

lemma validates_HilbertGrzPoint3 : FrameClass.finite_connected_partial_order.Validates Hilbert.GrzPoint3.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _, _, _⟩ φ (rfl | rfl);
  . apply validate_AxiomGrz_of_finite_strict_preorder;
    . assumption;
    . assumption;
    . assumption;
  . exact validate_AxiomPoint3_of_connected $ by assumption;

end FrameClass.finite_connected_partial_order

end Kripke


namespace Hilbert.GrzPoint3.Kripke

instance finite_sound : Sound (Hilbert.GrzPoint3) FrameClass.finite_connected_partial_order :=
  instSound_of_validates_axioms FrameClass.finite_connected_partial_order.validates_HilbertGrzPoint3

instance consistent : Entailment.Consistent (Hilbert.GrzPoint3) :=
  consistent_of_sound_frameclass FrameClass.finite_connected_partial_order (by simp)

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

end LO.Modal

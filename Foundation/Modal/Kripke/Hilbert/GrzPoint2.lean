import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.S4Point2

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

abbrev FrameClass.finite_confluent_partial_order : FrameClass := { F | F.IsFinite ∧ Reflexive F.Rel ∧ Transitive F.Rel ∧ AntiSymmetric F.Rel ∧ Confluent F.Rel }

namespace FrameClass.finite_confluent_partial_order

@[simp]
lemma nonempty : FrameClass.finite_confluent_partial_order.Nonempty := by
  use whitepoint;
  simp [Reflexive, Transitive, AntiSymmetric, Confluent ];
  infer_instance;

lemma validates_HilbertGrzPoint2 : FrameClass.finite_confluent_partial_order.Validates Hilbert.GrzPoint2.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _, _, _⟩ φ (rfl | rfl);
  . apply validate_AxiomGrz_of_finite_strict_preorder;
    . assumption;
    . assumption;
    . assumption;
  . exact validate_AxiomPoint2_of_confluent $ by assumption;

end FrameClass.finite_confluent_partial_order

end Kripke


namespace Hilbert.GrzPoint2.Kripke

instance finite_sound : Sound (Hilbert.GrzPoint2) FrameClass.finite_confluent_partial_order :=
  instSound_of_validates_axioms FrameClass.finite_confluent_partial_order.validates_HilbertGrzPoint2

instance consistent : Entailment.Consistent (Hilbert.GrzPoint2) :=
  consistent_of_sound_frameclass FrameClass.finite_confluent_partial_order (by simp)

instance finite_complete : Complete (Hilbert.GrzPoint2) FrameClass.finite_confluent_partial_order :=
  Kripke.Grz.complete_of_mem_miniCanonicalFrame FrameClass.finite_confluent_partial_order $ by
    sorry
    /-
    intro φ;
    refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm, ?_⟩;
    intro X Y Z ⟨⟨RXY₁, RXY₂⟩, ⟨RXZ₁, RXZ₂⟩⟩;
    obtain ⟨U, hU⟩ := ComplementClosedConsistentFinset.lindenbaum (𝓢 := Hilbert.GrzPoint2) (Φ := Y.1 ∪ Z.1) (Ψ := φ.subformulasGrz)
      (by
        apply Finset.union_subset_iff.mpr;
        constructor;
        . intro ψ hψ; exact Y.2.2 |>.subset hψ;
        . intro ψ hψ; exact Z.2.2 |>.subset hψ;
      )
      (by
        simp [FormulaFinset.Consistent];
        sorry;
      );
    use U;
    constructor;
    . constructor;
      . intro ψ _ hψY; exact hU $ Finset.mem_union.mpr (by tauto);
      . intro h;
        ext ξ;
        constructor;
        . intro hξY; exact hU $ Finset.mem_union.mpr (by tauto);
        . sorry;
    . constructor;
      . intro ψ _ hψZ; exact hU $ Finset.mem_union.mpr (by tauto);
      . intro h;
        ext ξ;
        constructor;
        . intro hξZ; exact hU $ Finset.mem_union.mpr (by tauto);
        . sorry;
    -/

end Hilbert.GrzPoint2.Kripke

end LO.Modal

import Foundation.Modal.Kripke.Logic.S4Point2McK
import Foundation.Modal.Kripke.Logic.S4Point3

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point3McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.IsPiecewiseConnected, F.SatisfiesMcKinseyCondition where

instance [F.IsS4Point3McK] : F.IsS4Point2McK where

protected abbrev FrameClass.S4Point3McK : FrameClass := { F | F.IsS4Point3McK }

end Kripke


namespace Logic.S4Point3McK.Kripke

instance : Sound (Hilbert.S4Point3McK) Kripke.FrameClass.S4Point3McK := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance : Entailment.Consistent Logic.S4Point3McK :=
  consistent_of_sound_frameclass Kripke.FrameClass.S4Point3McK $ by
    use whitepoint;
    constructor;

instance : Canonical (Hilbert.S4Point3McK) Kripke.FrameClass.S4Point3McK := ⟨by constructor⟩

instance : Complete (Hilbert.S4Point3McK) Kripke.FrameClass.S4Point3McK := inferInstance

lemma preorder_connected_mckinsey : Logic.S4Point3McK = Kripke.FrameClass.S4Point3McK.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4Point2McK ⪱ Logic.S4Point3McK := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.preorder_confluent_mckinsey ⊧ φ → FrameClass.S4Point3McK ⊧ φ by
      simpa [S4Point2McK.Kripke.preorder_confluent_mckinsey, S4Point3McK.Kripke.preorder_connected_mckinsey];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point3McK ⊢! φ ∧ ¬Kripke.FrameClass.preorder_confluent_mckinsey ⊧ φ by
      simpa [S4Point2McK.Kripke.preorder_confluent_mckinsey];
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 4, λ x y => x = 0 ∨ y = 3 ∨ x = y⟩,
        λ w a => match a with | 0 => w = 1 ∨ w = 3 | 1 => w = 2 ∨ w = 3 | _ => False
      ⟩;
      use M, 0;
      constructor
      . refine {
          refl := by omega,
          trans := by omega,
          mckinsey := by
            intro x;
            use 3;
            simp [Frame.Rel', M];
          ps_convergent := by
            intro x y z Rxy Ryz;
            use 3;
            tauto;
        }
      . suffices
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 1 ∨ w = 3) ∧ x ≠ 2 ∧ x ≠ 3) ∧
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 2 ∨ w = 3) ∧ x ≠ 1 ∧ x ≠ 3) by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        constructor;
        . use 1; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega;
        . use 2; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega;

instance : Logic.S4Point3 ⪱ Logic.S4Point3McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point3McK ⊢! φ ∧ ¬FrameClass.S4Point3 ⊧ φ by simpa [S4Point3.Kripke.connected_preorder];
    use (Axioms.McK (.atom 0))
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . exact {
          refl := by tauto,
          trans := by tauto,
          ps_connected := by tauto;
        }
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        trivial;

end Logic.S4Point3McK.Kripke

end LO.Modal

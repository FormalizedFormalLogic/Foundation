import Foundation.Modal.Kripke.Logic.S4Point3M
import Foundation.Modal.Kripke.Logic.S4Point4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point4M (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesSobocinskiCondition, F.SatisfiesMcKinseyCondition where

instance [F.IsS4Point4M] : F.IsS4Point3M where

protected abbrev FrameClass.S4Point4M : FrameClass := { F | F.IsS4Point4M }


end Kripke


namespace Logic.S4Point4M.Kripke

instance sound : Sound Logic.S4Point4M FrameClass.S4Point4M := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance consistent : Entailment.Consistent Logic.S4Point4M :=
  consistent_of_sound_frameclass FrameClass.S4Point4M $ by
    use whitepoint;
    constructor;

instance canonical : Canonical Logic.S4Point4M FrameClass.S4Point4M := ⟨by constructor⟩

instance complete : Complete Logic.S4Point4M FrameClass.S4Point4M := inferInstance

lemma preorder_sobocinski_mckinsey : Logic.S4Point4M = FrameClass.S4Point4M.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4Point3M ⪱ Logic.S4Point4M := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.S4Point3M ⊧ φ → FrameClass.S4Point4M ⊧ φ by
      simpa [S4Point3M.Kripke.preorder_connected_mckinsey, S4Point4M.Kripke.preorder_sobocinski_mckinsey];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point4M ⊢! φ ∧ ¬Kripke.FrameClass.S4Point3M ⊧ φ by simpa [S4Point3M.Kripke.preorder_connected_mckinsey];
    use (Axioms.Point4 (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x ≤ y⟩, λ w a => w ≠ 1⟩;
      use M, 0;
      constructor
      . exact {
          refl := by omega,
          trans := by omega,
          mckinsey := by
            simp only [ne_eq, M];
            intro x;
            use 2;
            constructor <;> omega;
        }
      . suffices ∃ x, (0 : M) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M) ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 2;
        omega;

instance : Logic.S4Point4 ⪱ Logic.S4Point4M := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.McK (.atom 0))
    constructor;
    . simp;
    . suffices ¬FrameClass.S4Point4 ⊧ Axioms.McK (atom 0) by simpa [S4Point4.Kripke.preorder_sobocinski];
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . exact {
          refl := by tauto,
          trans := by tauto,
          sobocinski := by tauto
        }
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        trivial;

end Logic.S4Point4M.Kripke

end LO.Modal

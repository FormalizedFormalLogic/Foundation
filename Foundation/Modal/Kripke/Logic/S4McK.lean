import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomMcK
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4McK

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.S4McK : FrameClass := { F | F.IsS4McK }

end Kripke



namespace Logic.S4McK.Kripke

instance sound : Sound Logic.S4McK FrameClass.S4McK := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;

instance consistent : Entailment.Consistent Logic.S4McK := consistent_of_sound_frameclass FrameClass.S4McK $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor

instance canonical : Canonical Logic.S4McK FrameClass.S4McK := ⟨by constructor⟩

instance complete : Complete Logic.S4McK FrameClass.S4McK := inferInstance

lemma preorder_mckinsey : Logic.S4McK = FrameClass.S4McK.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4 ⪱ Logic.S4McK := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4McK ⊢! φ ∧ ¬FrameClass.S4 ⊧ φ by simpa [S4.Kripke.preorder];
    use (Axioms.McK (.atom 0));
    constructor;
    . exact axiomMcK!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by tauto;
          trans := by tauto;
        }
      . suffices ∃ x, x ≠ (0 : M.World) by simpa [M, Transitive, Reflexive, Semantics.Realize, Satisfies];
        use 1;
        trivial;

instance : Logic.K4McK ⪱ Logic.S4McK := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4McK ⊢! φ ∧ ¬FrameClass.K4McK ⊧ φ by simpa [K4McK.Kripke.trans_mckinsey];
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . exact {
          trans := by omega;
          mckinsey := by
            simp only [Fin.isValue, forall_eq, and_self, M];
            intro;
            use 1;
        }
      . simp [Semantics.Realize, Satisfies, M];

end Logic.S4McK.Kripke

end LO.Modal

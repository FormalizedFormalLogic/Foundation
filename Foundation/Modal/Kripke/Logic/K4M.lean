import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomMcK

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

class Frame.IsK4M (F : Kripke.Frame) extends F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.K4M : FrameClass := { F | F.IsK4M }

end Kripke


namespace Logic.K4M.Kripke

instance sound : Sound Logic.K4M FrameClass.K4M := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;

instance consistent : Entailment.Consistent Logic.K4M := consistent_of_sound_frameclass FrameClass.K4M $ by
  use whitepoint;
  constructor;

instance canonical : Canonical Logic.K4M FrameClass.K4M := ⟨by constructor⟩

instance complete : Complete Logic.K4M FrameClass.K4M := inferInstance

lemma trans_mckinsey : Logic.K4M = FrameClass.K4M.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K4 ⪱ Logic.K4M := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K4M ⊢! φ ∧ ¬FrameClass.K4 ⊧ φ by simpa [K4.Kripke.trans];
    use (Axioms.McK (.atom 0));
    constructor;
    . exact axiomMcK!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . simp only [Set.mem_setOf_eq]; refine { trans := by simp; }
      . simp [Semantics.Realize, Satisfies];

end Logic.K4M.Kripke

end LO.Modal

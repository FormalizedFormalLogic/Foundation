import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomM

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

class Frame.IsK4M (F : Kripke.Frame) extends F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.K4M : FrameClass := { F | F.IsK4M }

end Kripke

namespace Hilbert.K4M

instance Kripke.sound : Sound (Hilbert.K4M) FrameClass.K4M := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4M) := consistent_of_sound_frameclass FrameClass.K4M $ by
  use whitepoint;
  constructor;

instance Kripke.canonical : Canonical (Hilbert.K4M) FrameClass.K4M := ⟨by constructor⟩

instance Kripke.complete : Complete (Hilbert.K4M) FrameClass.K4M := inferInstance

end Hilbert.K4M

namespace Logic

open Formula
open Entailment
open Kripke

lemma K4M.Kripke.trans_mckinsey : Logic.K4M = FrameClass.K4M.logic := eq_hilbert_logic_frameClass_logic

theorem K4M.proper_extension_of_K4 : Logic.K4 ⊂ Logic.K4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4M ⊢! φ ∧ ¬FrameClass.K4 ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . simp only [Set.mem_setOf_eq]; refine { trans := by simp; }
      . simp [Semantics.Realize, Satisfies];

end Logic


end LO.Modal

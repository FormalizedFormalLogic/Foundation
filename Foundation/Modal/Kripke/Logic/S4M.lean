import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomM
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4M

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4M (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition where

abbrev FrameClass.S4M : FrameClass := { F | F.IsS4M }

end Kripke



namespace Hilbert.S4M

instance Kripke.sound : Sound Logic.S4M FrameClass.S4M := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;

instance Kripke.consistent : Entailment.Consistent Logic.S4M := consistent_of_sound_frameclass FrameClass.S4M $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor

instance Kripke.canonical : Canonical Logic.S4M FrameClass.S4M := ⟨by constructor⟩

instance Kripke.complete : Complete Logic.S4M FrameClass.S4M := inferInstance

end Hilbert.S4M

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4M.Kripke.preorder_mckinsey : Logic.S4M = FrameClass.S4M.logic := eq_hilbert_logic_frameClass_logic

@[simp]
instance : Logic.S4 ⪱ Logic.S4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4M ⊢! φ ∧ ¬FrameClass.S4 ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
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

@[simp]
instance : Logic.K4M ⪱ Logic.S4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4M ⊢! φ ∧ ¬FrameClass.K4M ⊧ φ by
      rw [K4M.Kripke.trans_mckinsey];
      tauto;
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

end Logic

end LO.Modal

import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomM
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4M

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.preorder_mckinsey : FrameClass := { F | F.IsPreorder ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.S4M

instance Kripke.sound : Sound (Hilbert.S4M) (Kripke.FrameClass.preorder_mckinsey) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4M) := consistent_of_sound_frameclass Kripke.FrameClass.preorder_mckinsey $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;

instance Kripke.canonical : Canonical (Hilbert.S4M) Kripke.FrameClass.preorder_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
  . infer_instance;
  . infer_instance;
⟩

instance Kripke.complete : Complete (Hilbert.S4M) Kripke.FrameClass.preorder_mckinsey := inferInstance

end Hilbert.S4M

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4M.Kripke.preorder_mckinsey : Logic.S4M = FrameClass.preorder_mckinsey.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4M.proper_extension_of_S4 : Logic.S4 ⊂ Logic.S4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4M ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . apply isPreorder_iff _ _ |>.mpr;
        refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> simp [M];
      . suffices ∃ x, x ≠ (0 : M.World) by simpa [M, Transitive, Reflexive, Semantics.Realize, Satisfies];
        use 1;
        trivial;

@[simp]
theorem S4M.proper_extension_of_K4M : Logic.K4M ⊂ Logic.S4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4M ⊢! φ ∧ ¬FrameClass.trans_mckinsey ⊧ φ by
      rw [K4M.Kripke.trans_mckinsey];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨?_⟩, ⟨?_⟩⟩;
        . omega;
        . simp [M, McKinseyCondition];
      . simp [Semantics.Realize, Satisfies, M];

end Logic

end LO.Modal

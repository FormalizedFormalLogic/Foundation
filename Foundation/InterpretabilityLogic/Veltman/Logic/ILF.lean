import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomW

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILF (F : Veltman.Frame) extends F.IsIL, F.HasAxiomW
protected abbrev FrameClass.ILF : FrameClass := { F | F.IsILF }

instance : trivialFrame.HasAxiomW where
  S_W w := by
    apply Finite.converseWellFounded_of_trans_irrefl';
    . infer_instance;
    . tauto;
    . intro x; simp [Frame.RS, Relation.Comp];
instance : trivialFrame.IsILF where

instance {F : Veltman.Frame} [F.IsIL] : F.IsILMinus_J1_J2_J5 where
instance {F : Veltman.Frame} [F.IsILMinus_J1_J2_J5] : F.IsILMinus_J2Plus_J5 where

end Veltman


open Hilbert.Basic

namespace ILF

instance Veltman.sound : Sound InterpretabilityLogic.ILF FrameClass.ILF := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILF := Veltman.consistent_of_sound_frameclass FrameClass.ILF $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILF

instance : InterpretabilityLogic.IL ⪱ InterpretabilityLogic.ILF := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.F (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      let F : Veltman.Frame := {
        toKripkeFrame := ⟨Fin 3, (· < ·)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := (w = 0 ∧ x ≠ 0 ∧ y ≠ 0) ∨ (w = 1 ∧ x = 2 ∧ y = 2)
        S_cond := by grind;
      }
      have : F.IsIL := {
        S_J1 := by dsimp [Frame.SRel', F]; omega;
        S_J2 := by dsimp [Frame.SRel', F]; omega;
        S_J4 := by dsimp [Frame.SRel', F]; omega;
        S_J5 := by dsimp [Frame.SRel', F]; omega;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . by_contra hC;
        have : ∀ (x : F.World), (1 : F.World) ≺ x → ¬x ≺[(0 : F.World)] 1 := by
          simpa [Frame.RS, Relation.Comp, flip]
          using Frame.HasAxiomW.of_validate_axiomF hC |>.S_W 0 |>.isIrrefl.irrefl 1;
        apply @this 2;
        . omega;
        . simp [Frame.SRel', F];

end LO.InterpretabilityLogic

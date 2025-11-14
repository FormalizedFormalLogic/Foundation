import Foundation.InterpretabilityLogic.Veltman.Logic.ILW
import Foundation.InterpretabilityLogic.Veltman.Logic.ILM₀

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILWM₀ (F : Veltman.Frame) extends F.IsILM₀, F.IsILW
protected abbrev FrameClass.ILWM₀ : FrameClass := { F | F.IsILWM₀ }

instance : trivialFrame.IsILWM₀ where

end Veltman


open Hilbert.Basic

namespace ILWM₀

instance Veltman.sound : Sound InterpretabilityLogic.ILWM₀ FrameClass.ILWM₀ := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILWM₀ := Veltman.consistent_of_sound_frameclass FrameClass.ILWM₀ $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILWM₀

instance : InterpretabilityLogic.ILM₀ ⪱ InterpretabilityLogic.ILWM₀ := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.W (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILM₀);
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
      have : F.IsILM₀ := {
        S_J1 := by dsimp [Frame.SRel', F]; omega;
        S_J2 := by dsimp [Frame.SRel', F]; omega;
        S_J4 := by dsimp [Frame.SRel', F]; omega;
        S_J5 := by dsimp [Frame.SRel', F]; omega;
        S_M₀ := by dsimp [Frame.SRel', F]; omega;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . by_contra hC;
        have : ∀ (x : F.World), (1 : F.World) ≺ x → ¬x ≺[(0 : F.World)] 1 := by
          simpa [Frame.RS, Relation.Comp, flip]
          using Frame.HasAxiomW.of_validate_axiomW hC |>.S_W 0 |>.isIrrefl.irrefl 1;
        apply @this 2;
        . omega;
        . simp [Frame.SRel', F];

end LO.InterpretabilityLogic

import Foundation.InterpretabilityLogic.Veltman.Logic.IL_W
import Foundation.InterpretabilityLogic.Veltman.Logic.IL_M₀

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsIL_M₀_W (F : Veltman.Frame) extends F.IsIL_M₀, F.IsIL_W
protected abbrev FrameClass.IL_M₀_W : FrameClass := { F | F.IsIL_M₀_W }

instance : trivialFrame.IsIL_M₀_W where

end Veltman


open Hilbert.Basic

namespace IL_M₀_W

instance Veltman.sound : Sound InterpretabilityLogic.IL_M₀_W FrameClass.IL_M₀_W := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.IL_M₀_W := Veltman.consistent_of_sound_frameclass FrameClass.IL_M₀_W $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL_M₀_W

instance : InterpretabilityLogic.IL_M₀ ⪱ InterpretabilityLogic.IL_M₀_W := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.W (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL_M₀);
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
      have : F.IsIL_M₀ := {
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
          using Frame.HasAxiomW.of_validate_axiomW hC |>.S_W 0 |>.Std.Irrefl.irrefl 1;
        apply @this 2;
        . omega;
        . simp [Frame.SRel', F];

end LO.InterpretabilityLogic

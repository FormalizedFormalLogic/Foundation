import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1
import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J2Plus

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J1_J2 (F : Veltman.Frame) extends F.HasAxiomJ1, F.HasAxiomJ2
protected abbrev FrameClass.ILMinus_J1_J2 : FrameClass := { F | F.IsILMinus_J1_J2 }

instance : trivialFrame.IsILMinus_J1_J2 where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J1_J2

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J1_J2 FrameClass.ILMinus_J1_J2 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J1_J2 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J1_J2 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J1_J2


instance : InterpretabilityLogic.ILMinus_J1 ⪱ InterpretabilityLogic.ILMinus_J1_J2 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J2 (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel := λ x y => x < y
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := (w < x ∧ x = y) ∨ (w < x ∧ x < y ∧ ¬(w = 0 ∧ x = 1 ∧ y = 3)),
        S_cond := by tauto;
      };
      constructor;
      . constructor;
        simp [Frame.SRel'];
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ2.of_validate_axiomJ2 hC |>.S_J2 (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        simp [Frame.SRel'] at this;

instance : InterpretabilityLogic.ILMinus_J2Plus ⪱ InterpretabilityLogic.ILMinus_J1_J2 := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa [Hilbert.Minimal.buildAxioms] using hφ) with (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J1 (.atom 0)) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J2Plus);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      let F : Veltman.Frame := {
        toKripkeFrame := ⟨Fin 2, (· < ·)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := False,
        S_cond := by tauto;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { S_J2 := by tauto, S_J4 := by tauto }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ1.of_validate_axiomJ1 hC |>.S_J1 (show (0 : F.World) ≺ 1 by omega);
        contradiction;

end LO.InterpretabilityLogic

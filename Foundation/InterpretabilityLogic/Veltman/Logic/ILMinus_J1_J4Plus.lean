module

public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1
public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J4Plus

@[expose] public section

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J1_J4Plus (F : Veltman.Frame) extends F.HasAxiomJ1, F.HasAxiomJ4
protected abbrev FrameClass.ILMinus_J1_J4Plus : FrameClass := { F | F.IsILMinus_J1_J4Plus }

instance : trivialFrame.IsILMinus_J1_J4Plus where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J1_J4Plus

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J1_J4Plus FrameClass.ILMinus_J1_J4Plus := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J1_J4Plus := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J1_J4Plus $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J1_J4Plus


instance : InterpretabilityLogic.ILMinus_J1 ⪱ InterpretabilityLogic.ILMinus_J1_J4Plus := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 3
          Rel := λ x y => x < y
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := w ≺ x,
        S_cond := by omega
      }
      constructor;
      . constructor;
        intro x y Rxy;
        simpa;
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ4.of_validate_axiomJ4Plus hC |>.S_J4 (w := 1) (x := 2) (y := 0) (by omega);
        contradiction;

instance : InterpretabilityLogic.ILMinus_J4Plus ⪱ InterpretabilityLogic.ILMinus_J1_J4Plus := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J1 (.atom 0)) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J4Plus);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := ⟨Fin 2, (· < ·)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := False,
        S_cond := by tauto;
      }
      constructor;
      . constructor; simp;
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ1.of_validate_axiomJ1 hC |>.S_J1 (w := 0) (x := 1) (by omega);
        contradiction;

end LO.InterpretabilityLogic
end

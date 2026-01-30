module

public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J4Plus
public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J5
public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J4Plus_J5

@[expose] public section

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J1_J4Plus_J5 (F : Veltman.Frame) extends F.HasAxiomJ1, F.HasAxiomJ4, F.HasAxiomJ5
protected abbrev FrameClass.ILMinus_J1_J4Plus_J5 : FrameClass := { F | F.IsILMinus_J1_J4Plus_J5 }

instance : trivialFrame.IsILMinus_J1_J4Plus_J5 where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J1_J4Plus_J5

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J1_J4Plus_J5 FrameClass.ILMinus_J1_J4Plus_J5 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J1_J4Plus_J5 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J1_J4Plus_J5 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J1_J4Plus_J5


instance : InterpretabilityLogic.ILMinus_J1_J4Plus ⪱ InterpretabilityLogic.ILMinus_J1_J4Plus_J5 := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J5 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1_J4Plus);
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
        S w x y := w ≺ x ∧ x = y
        S_cond := by omega;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by tauto;
          S_J4 := by simp [Frame.SRel'];
        }
      . by_contra hC;
        replace hC := Veltman.Frame.HasAxiomJ5.of_validate_axiomJ5 hC |>.S_J5 (show 0 < 1 by omega) (show 1 < 2 by omega);
        contradiction

instance : InterpretabilityLogic.ILMinus_J1_J5 ⪱ InterpretabilityLogic.ILMinus_J1_J4Plus_J5 := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1_J5);
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
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by tauto
          S_J5 := by tauto
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ4.of_validate_axiomJ4Plus hC |>.S_J4 (w := 1) (x := 2) (y := 0) (by omega);
        contradiction;

instance : InterpretabilityLogic.ILMinus_J4Plus_J5 ⪱ InterpretabilityLogic.ILMinus_J1_J4Plus_J5 := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J1 (.atom 0)) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J4Plus_J5);
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
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J4 := by simp;
          S_J5 := by omega;
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ1.of_validate_axiomJ1 hC |>.S_J1 (w := 0) (x := 1) (by omega);
        contradiction;

end LO.InterpretabilityLogic
end

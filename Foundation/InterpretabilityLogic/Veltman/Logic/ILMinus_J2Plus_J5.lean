module

public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J4Plus_J5
public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J2Plus

@[expose] public section

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J2Plus_J5 (F : Veltman.Frame) extends F.HasAxiomJ2, F.HasAxiomJ5
protected abbrev FrameClass.ILMinus_J2Plus_J5 : FrameClass := { F | F.IsILMinus_J2Plus_J5 }

instance : trivialFrame.IsILMinus_J2Plus_J5 where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J2Plus_J5

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J2Plus_J5 FrameClass.ILMinus_J2Plus_J5 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J2Plus_J5 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J2Plus_J5 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J2Plus_J5


instance : InterpretabilityLogic.ILMinus_J2Plus ⪱ InterpretabilityLogic.ILMinus_J2Plus_J5 := by
  constructor;
  . apply weakerThan_buildAxioms_of_subset; decide;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J5 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J2Plus);
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
        S _ _ _ := False
        S_cond := by tauto
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { S_J2 := by tauto, S_J4 := by tauto; }
      . by_contra hC;
        replace hC := Veltman.Frame.HasAxiomJ5.of_validate_axiomJ5 hC |>.S_J5 (show 0 < 1 by omega) (show 1 < 2 by omega);
        contradiction

instance : InterpretabilityLogic.ILMinus_J4Plus_J5 ⪱ InterpretabilityLogic.ILMinus_J2Plus_J5 := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa [Hilbert.Minimal.buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J2 (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J4Plus_J5);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel := λ x y => x = 0 ∧ (0 < y)
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by tauto;
          irrefl := by omega;
        }
        S w x y := (w = 0 ∧ 0 < x ∧ x < 3 ∧ y = x + 1),
        S_cond := by grind;
      };
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J4 := by simp only [Frame.SRel']; omega;
          S_J5 := by grind;
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ2.of_validate_axiomJ2 hC |>.S_J2 (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        simp [Frame.SRel'] at this;

end LO.InterpretabilityLogic
end

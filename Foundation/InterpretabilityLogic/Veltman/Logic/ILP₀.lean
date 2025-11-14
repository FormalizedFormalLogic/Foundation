import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomR

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILP₀ (F : Veltman.Frame) extends F.IsIL, F.HasAxiomR
protected abbrev FrameClass.ILP₀ : FrameClass := { F | F.IsILP₀ }

instance : trivialFrame.HasAxiomR where
  S_R := by tauto;
instance : trivialFrame.IsILP₀ where

end Veltman


open Hilbert.Basic

namespace ILP₀

instance Veltman.sound : Sound InterpretabilityLogic.ILP₀ FrameClass.ILP₀ := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILP₀ := Veltman.consistent_of_sound_frameclass FrameClass.ILP₀ $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILP₀

instance : InterpretabilityLogic.IL ⪱ InterpretabilityLogic.ILP₀ := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.P₀ (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      let F : Veltman.Frame := {
        toKripkeFrame := ⟨Fin 5, λ x y => (x = 0 ∧ 0 < y) ∨ (x = 1 ∧ y = 2) ∨ (x = 3 ∧ y = 4)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y :=
          (w = 0 ∧ 1 ≤ x ∧ x ≤ y) ∨
          (w = 1 ∧ x = 2 ∧ y = 2) ∨
          (w = 3 ∧ x = 4 ∧ y = 4)
        S_cond := by grind;
      }
      have : F.IsIL := {
        S_J1 := by dsimp [F]; omega;
        S_J2 {w x y z} := by dsimp [F]; omega;
        S_J4 {w x y} := by dsimp [F]; omega;
        S_J5 {w x y} := by dsimp [F]; omega;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . by_contra hC;
        have : F.SRel' 1 2 4 := Frame.HasAxiomR.of_validate_axiomP₀ hC |>.S_R (x := 0) (u := 3) (by tauto) (by tauto) (by tauto) (by tauto);
        simp [F, Frame.SRel'] at this;

end LO.InterpretabilityLogic

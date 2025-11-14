import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomM₀

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILM₀ (F : Veltman.Frame) extends F.IsIL, F.HasAxiomM₀
protected abbrev FrameClass.ILM₀ : FrameClass := { F | F.IsILM₀ }

instance : trivialFrame.IsILM₀ where
  S_M₀ := by tauto

end Veltman


open Hilbert.Basic

namespace ILM₀

instance Veltman.sound : Sound InterpretabilityLogic.ILM₀ FrameClass.ILM₀ := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILM₀ := Veltman.consistent_of_sound_frameclass FrameClass.ILM₀ $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILM₀

instance : InterpretabilityLogic.IL ⪱ InterpretabilityLogic.ILM₀ := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M₀ (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      let F : Veltman.Frame :=  {
        toKripkeFrame := {
          World := Fin 5
          Rel x y := (x = 0 ∧ 0 < y) ∨ (x = 1 ∧ y = 2) ∨ (x = 3 ∧ y = 4)
        }
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
        have : F.Rel' 1 4 := Veltman.Frame.HasAxiomM₀.of_validate_axiomM₀ hC |>.S_M₀ (a := 0) (c := 2) (d := 3) (by tauto) (by tauto) (by tauto) (by tauto);
        simp [F, Modal.Kripke.Frame.Rel'] at this;

end LO.InterpretabilityLogic

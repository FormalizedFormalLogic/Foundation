import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomP
import Foundation.InterpretabilityLogic.Veltman.Logic.ILRW

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILP (F : Veltman.Frame) extends F.IsIL, F.HasAxiomP
protected abbrev FrameClass.ILP : FrameClass := { F | F.IsILP }

instance : trivialFrame.IsILP where
  S_P := by tauto

end Veltman


open Hilbert.Basic

namespace ILP

instance Veltman.sound : Sound InterpretabilityLogic.ILP FrameClass.ILP := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILP := Veltman.consistent_of_sound_frameclass FrameClass.ILP $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILP

open Entailment in
instance : InterpretabilityLogic.ILRW ⪱ InterpretabilityLogic.ILP := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa using hφ) with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1, axiomJ2, axiomJ3, axiomJ4, axiomJ5, axiomR, axiomW,
    ];
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.P (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILRW);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel x y := (x = 0 ∧ 0 < y) ∨ (x = 1 ∧ y = 2)
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := (w = 0 ∧ 1 ≤ x ∧ x ≤ y) ∨ (w = 1 ∧ x = 2 ∧ y = 2)
        S_cond := by grind;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by grind;
          S_J2 := by grind;
          S_J4 := by grind;
          S_J5 := by grind;
          S_W {w} := by
            apply Finite.converseWellFounded_of_trans_irrefl';
            . infer_instance
            . rintro x y z ⟨a, Rxa, Sway⟩ ⟨b, Ryb, Rwbz⟩;
              use a;
              grind;
            . dsimp [Irreflexive, Frame.RS, Relation.Comp];
              push_neg;
              grind;
          S_R := by grind;
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomP.of_validate_axiomP hC |>.S_P (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        contradiction;

end LO.InterpretabilityLogic

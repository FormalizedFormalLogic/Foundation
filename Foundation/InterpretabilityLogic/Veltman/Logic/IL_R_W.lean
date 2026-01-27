module

public import Foundation.InterpretabilityLogic.Veltman.Logic.IL_R
public import Foundation.InterpretabilityLogic.Veltman.Logic.IL_W
public import Foundation.InterpretabilityLogic.Veltman.Logic.IL_M₀_W

@[expose] public section

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsIL_R_W (F : Veltman.Frame) extends F.IsIL, F.HasAxiomW, F.HasAxiomR
protected abbrev FrameClass.IL_R_W : FrameClass := { F | F.IsIL_R_W }

instance : trivialFrame.IsIL_R_W where

end Veltman


open Hilbert.Basic

namespace IL_R_W

instance Veltman.sound : Sound InterpretabilityLogic.IL_R_W FrameClass.IL_R_W := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.IL_R_W := Veltman.consistent_of_sound_frameclass FrameClass.IL_R_W $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL_R_W

open Entailment in
instance : InterpretabilityLogic.IL_M₀_W ⪱ InterpretabilityLogic.IL_R_W := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa using hφ) with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1, axiomJ2, axiomJ3, axiomJ4, axiomJ5, axiomW, axiomM₀,
    ];
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.R (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL_M₀_W);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      let F : Veltman.Frame := {
        toKripkeFrame := ⟨Fin 5, λ x y => (x = 0 ∧ 0 < y) ∨ (x = 1 ∧ (y = 2 ∨ y = 4)) ∨ (x = 3 ∧ y = 4)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by grind;
          irrefl := by grind;
        }
        S w x y :=
          (w = 0 ∧ 1 ≤ x ∧ x ≤ y) ∨
          (w = 1 ∧ ((x = 2 ∧ y = 2) ∨ (x = 4 ∧ y = 4))) ∨
          (w = 3 ∧ x = 4 ∧ y = 4)
        S_cond := by grind;
      }
      have : F.IsIL_M₀_W := {
        S_J1 := by grind;
        S_J2 := by grind;
        S_J4 := by grind;
        S_J5 := by grind;
        S_M₀ := by grind;
        S_W {w} := by
          apply Finite.converseWellFounded_of_trans_irrefl';
          . infer_instance
          . rintro x y z ⟨a, Rxa, Sway⟩ ⟨b, Ryb, Rwbz⟩;
            use a;
            constructor;
            . assumption;
            . dsimp [Frame.SRel', F] at *;
              omega;
          . dsimp [Irreflexive, Frame.RS, Relation.Comp];
            push_neg;
            grind;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . by_contra hC;
        have : F.SRel' 1 2 4 := Frame.HasAxiomR.of_validate_axiomR hC |>.S_R (x := 0) (u := 3) (by tauto) (by tauto) (by tauto) (by tauto);
        grind;

instance «IL_R ⪱ IL_R_W» : InterpretabilityLogic.IL_R ⪱ InterpretabilityLogic.IL_R_W := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.W (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL_R);
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
      have : F.IsIL_R := {
        S_J1 := by dsimp [Frame.SRel', F]; omega;
        S_J2 := by dsimp [Frame.SRel', F]; omega;
        S_J4 := by dsimp [Frame.SRel', F]; omega;
        S_J5 := by dsimp [Frame.SRel', F]; omega;
        S_R := by dsimp [Frame.SRel', F]; omega;
      }
      use F;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . by_contra hC;
        have : ∀ (x : F.World), (1 : F.World) ≺ x → ¬x ≺[(0 : F.World)] 1 := by
          simpa [Frame.RS, Relation.Comp, flip]
          using Frame.HasAxiomW.of_validate_axiomW hC |>.S_W 0 |>.isIrrefl.irrefl 1;
        apply @this 2 <;> grind;

end LO.InterpretabilityLogic
end

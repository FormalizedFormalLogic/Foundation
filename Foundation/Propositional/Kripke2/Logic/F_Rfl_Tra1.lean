import Foundation.Propositional.Kripke2.Logic.F_Rfl
import Foundation.Propositional.Kripke2.Logic.F_Tra1

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected class Frame.IsF_Rfl_Tra1 (F : Kripke2.Frame) extends F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.F_Rfl_Tra1 : Kripke2.FrameClass := { F | F.IsF_Rfl_Tra1 }

instance : trivialFrame.IsF_Rfl_Tra1 where

end Kripke2


namespace F_Rfl_Tra1

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Rfl_Tra1 FrameClass.F_Rfl_Tra1 := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;> simp;

instance : Entailment.Consistent Propositional.F_Rfl_Tra1 := consistent_of_sound_frameclass FrameClass.F_Rfl_Tra1 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Rfl_Tra1

instance : Propositional.F_Rfl ⪱ Propositional.F_Rfl_Tra1 := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Tra1 #0 #1 #2);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Rfl);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 4, λ x y => x = y ∨ x = 0 ∨ y = x + 1, 0, by simp⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { refl := by omega; }
      . by_contra hC;
        simpa using IsTransitive_of_valid_axiomTra₁ hC |>.trans 1 2 3 (by omega) (by omega);

instance : Propositional.F_Tra1 ⪱ Propositional.F_Rfl_Tra1 := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Tra1);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x = 0), 0, by simp⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { trans := by simp }
      . by_contra hC;
        simpa using isReflexive_of_valid_axiomRfl hC |>.refl 1;

end LO.Propositional

import Foundation.Propositional.Kripke2.Logic.F_Rfl
import Foundation.Propositional.Kripke2.Logic.F_Sym

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected class Frame.IsF_Rfl_Sym (F : Kripke2.Frame) extends F.IsReflexive, F.IsSymmetric where
protected abbrev FrameClass.F_Rfl_Sym : Kripke2.FrameClass := { F | F.IsF_Rfl_Sym }

instance : trivialFrame.IsF_Rfl_Sym where

end Kripke2


namespace F_Rfl_Sym

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Rfl_Sym FrameClass.F_Rfl_Sym := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;> simp;

instance : Entailment.Consistent Propositional.F_Rfl_Sym := consistent_of_sound_frameclass FrameClass.F_Rfl_Sym $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Rfl_Sym

instance : Propositional.F_Rfl ⪱ Propositional.F_Rfl_Sym := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Sym #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Rfl);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x ≤ y), 0, by simp⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { refl := by omega; }
      . by_contra hC;
        simpa using isSymmetric_of_valid_axiomSym hC |>.symm 0 1;

instance : Propositional.F_Sym ⪱ Propositional.F_Rfl_Sym := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F_Sym);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x = 0 ∨ x ≠ y), 0, by simp⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { symm := by omega; }
      . by_contra hC;
        simpa using isReflexive_of_valid_axiomRfl hC |>.refl 1;

end LO.Propositional

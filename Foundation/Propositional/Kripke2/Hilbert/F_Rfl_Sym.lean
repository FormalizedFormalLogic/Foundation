module

public import Foundation.Propositional.Kripke2.Hilbert.F_Rfl
public import Foundation.Propositional.Kripke2.Hilbert.F_Sym

@[expose] public section

namespace LO.Propositional

open Kripke2


namespace Kripke2

protected class Frame.IsF_Rfl_Sym (F : Kripke2.Frame) extends F.IsReflexive, F.IsSymmetric where
protected abbrev FrameClass.F_Rfl_Sym : Kripke2.FrameClass := { F | F.IsF_Rfl_Sym }

instance : trivialFrame.IsF_Rfl_Sym where

end Kripke2


namespace HilbertF.F_Rfl_Sym

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Rfl_Sym : HilbertF ℕ) ({ F | F.IsF_Rfl_Sym } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;> simp;

instance : Entailment.Consistent (HilbertF.F_Rfl_Sym : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end HilbertF.F_Rfl_Sym

instance : (HilbertF.F_Rfl : HilbertF ℕ) ⪱ HilbertF.F_Rfl_Sym := by
  constructor;
  . grind;
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
        have := isSymmetric_of_valid_axiomSym hC |>.symm 0 1;
        grind;

instance : (HilbertF.F_Sym : HilbertF ℕ) ⪱ HilbertF.F_Rfl_Sym := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := ({ F | F.IsSymmetric } : Kripke2.FrameClass));
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x = 0 ∨ x ≠ y), 0, by simp⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact { symm := by omega; }
      . by_contra hC;
        have := isReflexive_of_valid_axiomRfl hC |>.refl 1;
        grind;

end LO.Propositional
end

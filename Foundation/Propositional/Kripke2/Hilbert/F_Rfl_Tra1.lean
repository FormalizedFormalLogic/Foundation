module

public import Foundation.Propositional.Kripke2.Hilbert.F_Rfl
public import Foundation.Propositional.Kripke2.Hilbert.F_Tra1

@[expose] public section

namespace LO.Propositional

open Kripke2


namespace Kripke2

protected class Frame.IsF_Rfl_Tra1 (F : Kripke2.Frame) extends F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.F_Rfl_Tra1 : Kripke2.FrameClass := { F | F.IsF_Rfl_Tra1 }

instance : trivialFrame.IsF_Rfl_Tra1 where

end Kripke2


namespace HilbertF.F_Rfl_Tra1

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Rfl_Tra1 : HilbertF ℕ) ({ F | F.IsF_Rfl_Tra1 } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩) <;> simp;

instance : Entailment.Consistent (HilbertF.F_Rfl_Tra1 : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end HilbertF.F_Rfl_Tra1

instance : (HilbertF.F_Rfl : HilbertF ℕ) ⪱ HilbertF.F_Rfl_Tra1 := by
  constructor;
  . grind;
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
        have := IsTransitive_of_valid_axiomTra₁ hC |>.trans 1 2 3 (by omega) (by omega);
        grind;

instance : (HilbertF.F_Tra1 : HilbertF ℕ) ⪱ HilbertF.F_Rfl_Tra1 := by
  constructor;
  . grind;
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
end

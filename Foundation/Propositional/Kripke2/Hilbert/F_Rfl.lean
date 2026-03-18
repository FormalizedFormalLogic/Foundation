module

public import Foundation.Propositional.Kripke2.Hilbert.F_Ser
public import Foundation.Propositional.Kripke2.Axiom.Rfl

@[expose] public section

namespace LO.Propositional

open Kripke2


namespace Kripke2

protected abbrev FrameClass.F_Rfl : Kripke2.FrameClass := { F | F.IsReflexive }

instance : trivialFrame.IsReflexive where
  refl := by simp

end Kripke2


namespace HilbertF.F_Rfl

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Rfl : HilbertF ℕ) ({ F | F.IsReflexive } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with ⟨_, _, rfl⟩;
  simp;

instance : Entailment.Consistent (HilbertF.F_Rfl : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance completeKripke2 : Complete (HilbertF.F_Rfl : HilbertF ℕ) ({ F | F.IsReflexive } : Kripke2.FrameClass) := by sorry;

end HilbertF.F_Rfl

instance : (HilbertF.F_Ser : HilbertF ℕ) ⪱ HilbertF.F_Rfl := by
  constructor;
  . apply HilbertF.Kripke2.weakerThan_of_subset_frameClass HilbertF.F_Ser.soundKripke2 HilbertF.F_Rfl.completeKripke2;
    rintro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := ({ F | F.IsSerial } : Kripke2.FrameClass));
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x = 0 ∨ x ≠ y), 0, by simp⟩;
      constructor;
      . exact {
          serial x := by
            match x with
            | 0 => use 1; omega;
            | 1 => use 0; omega;
        }
      . by_contra hC;
        have := isReflexive_of_valid_axiomRfl hC |>.refl 1;
        grind;

end LO.Propositional
end

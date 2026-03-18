module

public import Foundation.Propositional.Kripke2.Hilbert.F_Ser
public import Foundation.Propositional.Kripke2.Axiom.Sym

@[expose] public section

namespace LO.Propositional

open Kripke2

namespace Kripke2

instance : trivialFrame.IsSymmetric where
  symm := by simp

end Kripke2


namespace HilbertF.F_Sym

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Sym : HilbertF ℕ) ({ F | F.IsSymmetric } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with ⟨_, _, rfl⟩;
  simp;

instance : Entailment.Consistent (HilbertF.F_Sym : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end HilbertF.F_Sym

instance : (HilbertF.F : HilbertF ℕ) ⪱ HilbertF.F_Sym := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Sym #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x < y ∨ x = 0), 0, by simp⟩;
      constructor;
      . tauto;
      . by_contra hC;
        have := isSymmetric_of_valid_axiomSym hC |>.symm 0 1;
        simp at this;

end LO.Propositional
end

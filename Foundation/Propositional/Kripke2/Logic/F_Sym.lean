import Foundation.Propositional.Kripke2.Logic.F_Ser
import Foundation.Propositional.Kripke2.AxiomSym

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected abbrev FrameClass.F_Sym : Kripke2.FrameClass := { F | F.IsSymmetric }

instance : trivialFrame.IsSymmetric where
  symm := by simp

end Kripke2


namespace F_Sym

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Sym FrameClass.F_Sym := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with ⟨_, _, rfl⟩;
  simp;

instance : Entailment.Consistent Propositional.F_Sym := consistent_of_sound_frameclass FrameClass.F_Sym $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Sym

instance : Propositional.F ⪱ Propositional.F_Sym := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
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

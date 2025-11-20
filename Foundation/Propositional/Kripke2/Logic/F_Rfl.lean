import Foundation.Propositional.Kripke2.Logic.F
import Foundation.Propositional.Kripke2.AxiomRfl

namespace LO.Propositional

open Hilbert.Corsi
open Kripke2


namespace Kripke2

protected class Frame.IsF_Rfl (F : Kripke2.Frame) extends F.IsReflexive where
protected abbrev FrameClass.F_Rfl : Kripke2.FrameClass := { F | F.IsF_Rfl }

instance : trivialFrame.IsF_Rfl where
  refl := by simp

end Kripke2


namespace F_Rfl

open Hilbert.Corsi.Kripke2

instance Kripke2.sound : Sound Propositional.F_Rfl FrameClass.F_Rfl := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl);
  simp;

instance : Entailment.Consistent Propositional.F_Rfl := consistent_of_sound_frameclass FrameClass.F_Rfl $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end F_Rfl

instance : Propositional.F ⪱ Propositional.F_Rfl := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Rfl #0 #1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x < y ∨ x = 0), 0, by simp⟩;
      constructor;
      . tauto;
      . by_contra hC;
        simpa using isReflexive_of_valid_axiomRfl hC |>.refl 1;

end LO.Propositional

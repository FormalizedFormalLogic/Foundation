module
import Foundation.Propositional.Kripke2.Logic.F
import Foundation.Propositional.Kripke2.AxiomSer

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected abbrev FrameClass.F_Ser : Kripke2.FrameClass := { F | F.IsSerial }

instance : trivialFrame.IsSerial where
  serial := by tauto;

end Kripke2


namespace F_Ser

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Ser FrameClass.F_Ser := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl);
  simp;

instance : Entailment.Consistent Propositional.F_Ser := consistent_of_sound_frameclass FrameClass.F_Ser $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

/-
instance Kripke2.complete : Complete Propositional.F_Ser FrameClass.F_Ser := by
  constructor;
  intro φ hφ;
  apply Kripke2.provable_of_validOncanonicalModel;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
-/

end F_Ser

instance : Propositional.F ⪱ Propositional.F_Ser := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Ser;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x < y ∨ x = 0), 0, by simp⟩;
      constructor;
      . tauto;
      . by_contra hC;
        simpa using isSerial_of_valid_axiomSer hC |>.serial 1;

end LO.Propositional

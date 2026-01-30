module

public import Foundation.Propositional.Kripke2.Logic.F_Ser
public import Foundation.Propositional.Kripke2.AxiomTra

@[expose] public section

namespace LO.Propositional

open Hilbert.F
open Kripke2


namespace Kripke2

protected abbrev FrameClass.F_Tra1 : Kripke2.FrameClass := { F | F.IsTransitive }

instance : trivialFrame.IsTransitive where
  trans := by simp

end Kripke2


namespace F_Tra1

open Hilbert.F.Kripke2

instance Kripke2.sound : Sound Propositional.F_Tra1 FrameClass.F_Tra1 := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with ⟨_, _, _, rfl⟩;
  simp;

instance : Entailment.Consistent Propositional.F_Tra1 := consistent_of_sound_frameclass FrameClass.F_Tra1 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

/-
instance Kripke2.complete : Complete Propositional.F_Tra1 FrameClass.F_Tra1 := by
  constructor;
  intro φ hφ;
  apply Kripke2.provable_of_validOncanonicalModel;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
-/

end F_Tra1

instance : Propositional.F ⪱ Propositional.F_Tra1 := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Tra1 #0 #1 #2);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke2.FrameClass.F);
      apply Kripke2.not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 2, (λ x y => x = 0 ∨ x ≠ y), 0, by simp⟩;
      constructor;
      . tauto;
      . by_contra hC;
        simpa using IsTransitive_of_valid_axiomTra₁ hC |>.trans 1;


end LO.Propositional
end

module

public import Foundation.Propositional.Kripke2.Hilbert.F_Ser
public import Foundation.Propositional.Kripke2.Axiom.Tra

@[expose] public section

namespace LO.Propositional

open Kripke2


namespace Kripke2

protected abbrev FrameClass.F_Tra1 : Kripke2.FrameClass := { F | F.IsTransitive }

instance : trivialFrame.IsTransitive where
  trans := by simp

end Kripke2


namespace HilbertF.F_Tra1

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Tra1 : HilbertF ℕ) ({ F | F.IsTransitive } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with ⟨_, _, _, rfl⟩;
  simp;

instance : Entailment.Consistent (HilbertF.F_Tra1 : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
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

end HilbertF.F_Tra1

instance : (HilbertF.F : HilbertF ℕ) ⪱ HilbertF.F_Tra1 := by
  constructor;
  . grind;
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

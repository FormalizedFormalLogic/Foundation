module

public import Foundation.Propositional.Kripke2.Hilbert.F
public import Foundation.Propositional.Kripke2.Axiom.Ser

@[expose] public section

namespace LO.Propositional

open Kripke2

namespace Kripke2

instance : trivialFrame.IsSerial where
  serial := by tauto;

end Kripke2


namespace HilbertF.F_Ser

open Kripke2

instance soundKripke2 : Sound (HilbertF.F_Ser : HilbertF ℕ) ({ F | F.IsSerial } : Kripke2.FrameClass) := by
  apply instFrameClassSound;
  constructor;
  rintro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl);
  simp;

instance : Entailment.Consistent (HilbertF.F_Ser : HilbertF ℕ) := consistent_of_sound_frameclass soundKripke2 $ by
  use Kripke2.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end HilbertF.F_Ser


instance : (HilbertF.F : HilbertF ℕ) ⪱ HilbertF.F_Ser := by
  constructor;
  . grind;
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
end

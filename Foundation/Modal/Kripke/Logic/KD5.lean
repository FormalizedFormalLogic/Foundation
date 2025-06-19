import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K5
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

protected class Frame.IsKD5 (F : Kripke.Frame) extends F.IsSerial, F.IsEuclidean
protected abbrev FrameClass.KD5 : FrameClass := { F | F.IsKD5 }

end Kripke


namespace Hilbert.KD5.Kripke

instance sound : Sound (Hilbert.KD5) Kripke.FrameClass.KD5 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KD5) := consistent_of_sound_frameclass Kripke.FrameClass.KD5 $ by
  use whitepoint;
  constructor;


instance canonical : Canonical (Hilbert.KD5) Kripke.FrameClass.KD5 := ⟨by constructor⟩

instance complete : Complete (Hilbert.KD5) Kripke.FrameClass.KD5 := inferInstance

end Hilbert.KD5.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma KD5.Kripke.serial_eucl : Logic.KD5 = Kripke.FrameClass.KD5.logic := eq_hilbert_logic_frameClass_logic

theorem KD5.proper_extension_of_KD : Logic.KD ⊂ Logic.KD5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> tauto;

theorem KD5.proper_extension_of_K5 : Logic.K5 ⊂ Logic.KD5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬Kripke.FrameClass.K5 ⊧ φ by
      rw [K5.Kripke.eucl];
      tauto;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine { reucl := by simp [RightEuclidean]; };
      . simp [Semantics.Realize, Satisfies];


end Logic

end LO.Modal

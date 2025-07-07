import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K5
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKD5 (F : Kripke.Frame) extends F.IsSerial, F.IsEuclidean
protected abbrev FrameClass.KD5 : FrameClass := { F | F.IsKD5 }

end Kripke


namespace Logic.KD5.Kripke

instance sound : Sound (Logic.KD5) Kripke.FrameClass.KD5 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Logic.KD5) := consistent_of_sound_frameclass Kripke.FrameClass.KD5 $ by
  use whitepoint;
  constructor;

instance canonical : Canonical (Logic.KD5) Kripke.FrameClass.KD5 := ⟨by constructor⟩

instance complete : Complete (Logic.KD5) Kripke.FrameClass.KD5 := inferInstance

lemma serial_eucl : Logic.KD5 = Kripke.FrameClass.KD5.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.KD ⪱ Logic.KD5 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KD5 ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by simpa [KD.Kripke.serial];
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

instance : Logic.K5 ⪱ Logic.KD5 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KD5 ⊢! φ ∧ ¬Kripke.FrameClass.K5 ⊧ φ by
      simpa [K5.Kripke.eucl];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine { reucl := by simp [RightEuclidean]; };
      . simp [Semantics.Realize, Satisfies];

end Logic.KD5.Kripke

end LO.Modal

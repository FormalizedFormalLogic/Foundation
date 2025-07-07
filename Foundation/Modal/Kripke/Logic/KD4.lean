import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKD4 (F : Kripke.Frame) extends F.IsSerial, F.IsTransitive

protected abbrev FrameClass.KD4 : FrameClass := { F | F.IsKD4 }

end Kripke


namespace Logic.KD4.Kripke

instance sound : Sound Logic.KD4 FrameClass.KD4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent Logic.KD4 := consistent_of_sound_frameclass
  FrameClass.KD4 $ by
    use whitepoint;
    constructor

instance canonical : Canonical Logic.KD4 FrameClass.KD4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor
⟩

instance complete : Complete Logic.KD4 FrameClass.KD4 := inferInstance

lemma serial_trans : Logic.KD4 = FrameClass.KD4.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.KD ⪱ Logic.KD4 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KD4 ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by
      simpa [KD.Kripke.serial];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . exact { serial := by simp [Serial]; };
      . simp [Semantics.Realize, Satisfies];
        tauto;

instance : Logic.K4 ⪱ Logic.KD4 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KD4 ⊢! φ ∧ ¬FrameClass.K4 ⊧ φ by
      simpa [K4.Kripke.trans];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . exact { trans := by simp; }
      . simp [Semantics.Realize, Satisfies];

end Logic.KD4.Kripke

end LO.Modal

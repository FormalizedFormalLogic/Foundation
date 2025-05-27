import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans : FrameClass := { F | IsSerial _ F ∧ IsTrans _ F }

namespace Hilbert.KD4.Kripke

instance sound : Sound (Hilbert.KD4) Kripke.FrameClass.serial_trans := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.KD4) := consistent_of_sound_frameclass
  Kripke.FrameClass.serial_trans $ by
    use whitepoint;
    constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KD4) Kripke.FrameClass.serial_trans := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KD4) Kripke.FrameClass.serial_trans := inferInstance

end Hilbert.KD4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KD4.Kripke.serial_trans : Logic.KD4 = FrameClass.serial_trans.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.KD Logic.KD4 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . refine ⟨by simp [Serial]⟩;
      . simp [Semantics.Realize, Satisfies];
        tauto;
⟩

instance : ProperSublogic Logic.K4 Logic.KD4 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

end Logic

end LO.Modal

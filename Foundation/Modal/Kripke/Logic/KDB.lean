import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KB
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_symm : FrameClass := { F | IsSerial _ F ∧ IsSymm _ F }

namespace Hilbert.KDB.Kripke

instance sound : Sound (Hilbert.KDB) Kripke.FrameClass.serial_symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KDB) := consistent_of_sound_frameclass Kripke.FrameClass.serial_symm $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KDB) Kripke.FrameClass.serial_symm := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KDB) Kripke.FrameClass.serial_symm := inferInstance

end Hilbert.KDB.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KDB.Kripke.serial_symm : Logic.KDB = FrameClass.serial_symm.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.KD Logic.KDB := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine ⟨?_⟩;
        intro x;
        match x with
        | 0 => use 1; tauto;
        | 1 => use 1;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor <;> omega;
⟩

instance : ProperSublogic Logic.KB Logic.KDB := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.symm ⊧ φ by
      rw [KB.Kripke.symm];
      tauto;
    use Axioms.D (.atom 0);
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

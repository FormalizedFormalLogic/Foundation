import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KB
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKDB (F : Kripke.Frame) extends F.IsSerial, F.IsSymmetric

abbrev FrameClass.KDB : FrameClass := { F | F.IsKDB }

end Kripke


namespace Hilbert.KDB.Kripke

instance sound : Sound (Hilbert.KDB) Kripke.FrameClass.KDB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KDB) := consistent_of_sound_frameclass Kripke.FrameClass.KDB $ by
  use whitepoint;
  constructor;


instance canonical : Canonical (Hilbert.KDB) Kripke.FrameClass.KDB := ⟨by constructor⟩

instance complete : Complete (Hilbert.KDB) Kripke.FrameClass.KDB := inferInstance

end Hilbert.KDB.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KDB.Kripke.serial_symm : Logic.KDB = Kripke.FrameClass.KDB.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem KDB.proper_extension_of_KD : Logic.KD ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine { serial := by intro x; use 1; omega;}
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor <;> omega;

@[simp]
theorem KDB.proper_extension_of_KB : Logic.KB ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.KB ⊧ φ by
      rw [KB.Kripke.symm];
      tauto;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine { symm := by simp; };
      . simp [Semantics.Realize, Satisfies];

end Logic

end LO.Modal

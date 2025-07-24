import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.KB
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKDB (F : Kripke.Frame) extends F.IsSerial, F.IsSymmetric

abbrev FrameClass.KDB : FrameClass := { F | F.IsKDB }

end Kripke


namespace Hilbert.KDB.Kripke

instance : Sound (Hilbert.KDB) Kripke.FrameClass.KDB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomB_of_symmetric;

instance : Entailment.Consistent (Hilbert.KDB) := consistent_of_sound_frameclass Kripke.FrameClass.KDB $ by
  use whitepoint;
  constructor;


instance : Canonical (Hilbert.KDB) Kripke.FrameClass.KDB := ⟨by constructor⟩

instance : Complete (Hilbert.KDB) Kripke.FrameClass.KDB := inferInstance


instance : Hilbert.KD ⪱ Hilbert.KDB := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine { serial := by intro x; use 1; omega;}
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor <;> omega;

instance : Hilbert.KB ⪱ Hilbert.KDB := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KB)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine { symm := by simp; };
      . simp [Semantics.Realize, Satisfies];

end Hilbert.KDB.Kripke

instance : Modal.KD ⪱ Modal.KDB := inferInstance

instance : Modal.KB ⪱ Modal.KDB := inferInstance

end LO.Modal

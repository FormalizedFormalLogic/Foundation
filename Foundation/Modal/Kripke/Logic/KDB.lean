module
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.KB
import Foundation.Modal.Kripke.Logic.KD

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsKDB (F : Kripke.Frame) extends F.IsSerial, F.IsSymmetric

abbrev FrameClass.KDB : FrameClass := { F | F.IsKDB }

end Kripke


instance : Sound (Modal.KDB) Kripke.FrameClass.KDB := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomB_of_symmetric;

instance : Entailment.Consistent (Modal.KDB) := consistent_of_sound_frameclass Kripke.FrameClass.KDB $ by
  use whitepoint;
  constructor;

instance : Canonical (Modal.KDB) Kripke.FrameClass.KDB := ⟨by constructor⟩

instance : Complete (Modal.KDB) Kripke.FrameClass.KDB := inferInstance

instance : Modal.KD ⪱ Modal.KDB := by
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
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [M, Semantics.Models, Satisfies];
        use 1;
        constructor <;> omega;

instance : Modal.KB ⪱ Modal.KDB := by
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
      . simp [Semantics.Models, Satisfies];

end LO.Modal

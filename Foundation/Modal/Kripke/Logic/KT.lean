import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KD
import Foundation.Modal.Entailment.KT

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

protected abbrev Frame.IsKT := Frame.IsReflexive

protected abbrev FrameClass.KT : FrameClass := { F | F.IsKT }

instance {F : Kripke.Frame} [F.IsKT] : F.IsKD := by simp

end Kripke


namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) FrameClass.KT := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_refl _ rfl;
  exact Kripke.validate_AxiomT_of_reflexive (refl := F_refl);

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) := consistent_of_sound_frameclass FrameClass.KT $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  simp;

instance Kripke.canonical : Canonical (Hilbert.KT) FrameClass.KT := ⟨by
  apply Set.mem_setOf_eq.mpr;
  dsimp [Frame.IsKT];
  infer_instance;
⟩

instance Kripke.complete : Complete (Hilbert.KT) FrameClass.KT := inferInstance

end Hilbert.KT

namespace Logic

open Formula
open Entailment
open Kripke

lemma KT.Kripke.refl : Logic.KT = FrameClass.KT.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem KT.proper_extension_of_KD : Logic.KD ⊂ Logic.KT := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KT ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { serial := by tauto };
      . simp [Semantics.Realize, Satisfies];

end Logic

end LO.Modal

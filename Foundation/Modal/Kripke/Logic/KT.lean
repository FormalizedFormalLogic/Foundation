import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KD
import Foundation.Modal.Entailment.KT

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev Frame.IsKT := Frame.IsReflexive

protected abbrev FrameClass.KT : FrameClass := { F | F.IsKT }

instance {F : Kripke.Frame} [F.IsKT] : F.IsKD := by simp

end Kripke


namespace Logic.KT.Kripke

instance sound : Sound Logic.KT FrameClass.KT := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_refl _ rfl;
  exact Kripke.validate_AxiomT_of_reflexive (refl := F_refl);

instance consistent : Entailment.Consistent Logic.KT := consistent_of_sound_frameclass FrameClass.KT $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  simp;

instance canonical : Canonical Logic.KT FrameClass.KT := ⟨by
  apply Set.mem_setOf_eq.mpr;
  dsimp [Frame.IsKT];
  infer_instance;
⟩

instance complete : Complete Logic.KT FrameClass.KT := inferInstance

lemma refl : Logic.KT = FrameClass.KT.logic := eq_hilbert_logic_frameClass_logic

@[simp]
instance : Logic.KD ⪱ Logic.KT := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KT ⊢! φ ∧ ¬FrameClass.IsKD ⊧ φ by
      simpa [KD.Kripke.serial];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { serial := by tauto };
      . simp [Semantics.Realize, Satisfies];

end Logic.KT.Kripke

end LO.Modal

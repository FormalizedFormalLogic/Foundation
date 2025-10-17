import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Logic.KD
import Foundation.Modal.Entailment.KT

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected abbrev Frame.IsKT := Frame.IsReflexive

protected abbrev FrameClass.KT : FrameClass := { F | F.IsKT }

instance {F : Kripke.Frame} [F.IsKT] : F.IsKD := by simp

end Kripke


instance : Sound Modal.KT FrameClass.KT := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F F_refl;
  exact Kripke.validate_AxiomT_of_reflexive (refl := F_refl);

instance : Entailment.Consistent Modal.KT := consistent_of_sound_frameclass FrameClass.KT $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  simp;

instance : Canonical Modal.KT FrameClass.KT := ⟨by
  apply Set.mem_setOf_eq.mpr;
  dsimp [Frame.IsKT];
  infer_instance;
⟩

instance : Complete Modal.KT FrameClass.KT := inferInstance

instance : Modal.KD ⪱ Modal.KT := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl);
    . simp;
    . simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KD)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { serial := by tauto };
      . simp [Semantics.Realize, Satisfies];

end LO.Modal

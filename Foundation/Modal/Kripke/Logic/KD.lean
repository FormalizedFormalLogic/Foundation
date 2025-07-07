import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev Frame.IsKD := Frame.IsSerial

protected abbrev FrameClass.IsKD : FrameClass := { F | F.IsKD }

end Kripke


namespace Logic.KD.Kripke

instance sound : Sound Logic.KD FrameClass.IsKD :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F F_serial φ rfl;
    apply validate_AxiomD_of_serial (ser := F_serial);

instance consistent : Entailment.Consistent Logic.KD :=
  consistent_of_sound_frameclass FrameClass.IsKD $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance canonical : Canonical Logic.KD FrameClass.IsKD := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Logic.KD FrameClass.IsKD := inferInstance

end Logic.KD.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KD.Kripke.serial : Logic.KD = FrameClass.IsKD.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K ⪱ Logic.KD := by
  constructor;
  . infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KD ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.Kripke.all];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . trivial;
      . simp [Semantics.Realize, Satisfies];

end Logic

end LO.Modal

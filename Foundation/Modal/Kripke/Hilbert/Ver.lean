import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Hilbert.Basic

namespace LO.Modal

open Kripke
open Hilbert.Kripke

protected abbrev Kripke.FrameClass.isolated : FrameClass := { F | IsIsolated _ F }
protected abbrev Kripke.FrameClass.finite_isolated : FrameClass := { F | Finite F.World ∧ IsIsolated _ F }

namespace Hilbert.Ver.Kripke

instance sound : Sound (Hilbert.Ver) FrameClass.isolated := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F hF _ (rfl | rfl);
  have := Set.mem_setOf_eq.mp hF;
  exact Kripke.validate_AxiomVer_of_isolated (F := F);

instance sound_finite_isolated : Sound (Hilbert.Ver) Kripke.FrameClass.finite_isolated :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F ⟨_, _⟩ _ (rfl | rfl);
    exact validate_AxiomVer_of_isolated (F := F);

instance consistent : Entailment.Consistent (Hilbert.Ver) := consistent_of_sound_frameclass FrameClass.isolated $ by
  use blackpoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Kripke.Canonical (Hilbert.Ver) FrameClass.isolated := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.Ver) FrameClass.isolated := inferInstance

instance complete_finite_isolated : Complete (Hilbert.Ver) Kripke.FrameClass.finite_isolated := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  intro F ⟨F_iso⟩ V r;
  apply Model.pointGenerate.modal_equivalent_at_root (r := r) |>.mp;
  apply hφ;
  refine ⟨?_, ?_⟩;
  . apply finite_iff_exists_equiv_fin.mpr;
    use 1;
    constructor;
    trans Unit;
    . refine ⟨λ _ => (), λ _ => ⟨r, by tauto⟩, ?_, ?_⟩
      . simp [Function.LeftInverse];
        intro x Rrx;
        exfalso;
        induction Rrx with
        | single h => exact F_iso h;
        | tail _ h => exact F_iso h;
      . simp [Function.RightInverse, Function.LeftInverse];
    . exact finOneEquiv.symm;
  . apply isIsolated_iff _ _ |>.mpr;
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ <;> apply F_iso;
⟩

end Hilbert.Ver.Kripke

lemma Logic.Ver.Kripke.isolated : Logic.Ver = FrameClass.isolated.logic := eq_hilbert_logic_frameClass_logic
lemma Logic.Ver.Kripke.finite_isolated : Logic.Ver = FrameClass.finite_isolated.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

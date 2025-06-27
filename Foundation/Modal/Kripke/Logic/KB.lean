import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev Frame.IsKB := Frame.IsSymmetric
protected abbrev FrameClass.KB : FrameClass := { F | F.IsKB }

end Kripke



namespace Logic.KB.Kripke

instance sound : Sound Logic.KB FrameClass.KB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_symm _ rfl;
  exact validate_AxiomB_of_symmetric (sym := F_symm);

instance consistent : Entailment.Consistent Logic.KB := consistent_of_sound_frameclass FrameClass.KB $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical Logic.KB FrameClass.KB := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Logic.KB FrameClass.KB := inferInstance

lemma symm : Logic.KB = FrameClass.KB.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K ⪱ Logic.KB := by

  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KB ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      simpa [K.Kripke.all];
    use (Axioms.B (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;

end Logic.KB.Kripke

end LO.Modal

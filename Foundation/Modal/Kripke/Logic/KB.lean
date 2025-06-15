import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Kripke
open Hilbert.Kripke



protected abbrev Kripke.FrameClass.symm : FrameClass := { F | F.IsSymmetric }

namespace Hilbert.KB.Kripke

instance sound : Sound (Hilbert.KB) Kripke.FrameClass.symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_symm _ rfl;
  exact validate_AxiomB_of_symmetric (sym := F_symm);

instance consistent : Entailment.Consistent (Hilbert.KB) := consistent_of_sound_frameclass FrameClass.symm $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.KB) Kripke.FrameClass.symm := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KB) Kripke.FrameClass.symm := inferInstance

end Hilbert.KB.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KB.Kripke.symm : Logic.KB = FrameClass.symm.logic := eq_hilbert_logic_frameClass_logic

theorem KB.proper_extension_of_K : Logic.K ⊂ Logic.KB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      rw [K.Kripke.all];
      tauto;
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;

end Logic

end LO.Modal

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

protected abbrev Frame.IsKB := Frame.IsSymmetric
protected abbrev FrameClass.KB : FrameClass := { F | F.IsKB }

end Kripke



namespace Hilbert

namespace KB.Kripke

instance : Sound Hilbert.KB FrameClass.KB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_symm _ rfl;
  exact validate_AxiomB_of_symmetric (sym := F_symm);

instance : Entailment.Consistent Hilbert.KB := consistent_of_sound_frameclass FrameClass.KB $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical Hilbert.KB FrameClass.KB := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Hilbert.KB FrameClass.KB := inferInstance

end KB.Kripke

instance : Hilbert.K ⪱ Hilbert.KB := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.B (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.all)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;

end Hilbert

instance : Modal.K ⪱ Modal.KB := inferInstance

lemma KB.Kripke.eq_symm : Modal.KB = FrameClass.KB.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

module

public import Foundation.Modal.Kripke.Logic.K

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected abbrev Frame.IsKB := Frame.IsSymmetric
protected abbrev FrameClass.KB : FrameClass := { F | F.IsKB }

end Kripke



instance : Sound Modal.KB FrameClass.KB := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F F_symm;
  exact validate_AxiomB_of_symmetric (sym := F_symm);

instance : Entailment.Consistent Modal.KB := consistent_of_sound_frameclass FrameClass.KB $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical Modal.KB FrameClass.KB := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Modal.K ⪱ Modal.KB := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.B (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simp [Semantics.Models, Satisfies, M];
          grind;
        use 1;
        trivial;

end LO.Modal
end

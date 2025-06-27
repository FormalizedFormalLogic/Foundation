import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.AxiomPoint4

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point4 (F : Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesSobocinskiCondition

protected abbrev FrameClass.S4Point4 : FrameClass := { F | F.IsS4Point4 }

instance [F.IsS4Point4] : F.IsS4Point3 where

end Kripke


namespace Logic.S4Point4.Kripke

instance sound : Sound (Logic.S4Point4) Kripke.FrameClass.S4Point4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance consistent : Entailment.Consistent Logic.S4Point4 :=
  consistent_of_sound_frameclass Kripke.FrameClass.S4Point4 $ by
    use whitepoint;
    constructor;

instance canonical : Canonical (Logic.S4Point4) Kripke.FrameClass.S4Point4 := ⟨by constructor⟩

instance complete : Complete (Logic.S4Point4) Kripke.FrameClass.S4Point4 := inferInstance

lemma preorder_sobocinski : Logic.S4Point4 = Kripke.FrameClass.S4Point4.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4Point3 ⪱ Logic.S4Point4 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, S4Point3.Kripke.connected_preorder, S4Point4.Kripke.preorder_sobocinski];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point4 ⊢! φ ∧ ¬FrameClass.S4Point3 ⊧ φ by simpa [S4Point3.Kripke.connected_preorder];
    use Axioms.Point4 (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x ≤ y⟩,
        λ w a => w ≠ 1
      ⟩;
      use M, 0;
      constructor;
      . exact {};
      . suffices ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M.World) ≺ 1 by
          simpa [Semantics.Realize, Satisfies, M];
        use 2;
        omega;

end Logic.S4Point4.Kripke

end LO.Modal

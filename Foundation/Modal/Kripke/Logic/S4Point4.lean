import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.AxiomPoint4

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point4 (F : Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesSobocinskiCondition

protected abbrev FrameClass.S4Point4 : FrameClass := { F | F.IsS4Point4 }

instance [F.IsS4Point4] : F.IsS4Point3 where

end Kripke


namespace Hilbert.S4Point4.Kripke

instance sound : Sound (Hilbert.S4Point4) Kripke.FrameClass.S4Point4 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance consistent : Entailment.Consistent (Hilbert.S4Point4) :=
  consistent_of_sound_frameclass Kripke.FrameClass.S4Point4 $ by
    use whitepoint;
    constructor;

instance canonical : Canonical (Hilbert.S4Point4) Kripke.FrameClass.S4Point4 := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
⟩

instance complete : Complete (Hilbert.S4Point4) Kripke.FrameClass.S4Point4 := inferInstance

end Hilbert.S4Point4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point4.Kripke.preorder_sobocinski : Logic.S4Point4 = Kripke.FrameClass.S4Point4.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4Point4.proper_extension_of_S4Point3 : Logic.S4Point3 ⊂ Logic.S4Point4 := by
  constructor;
  . rw [S4Point3.Kripke.connected_preorder, S4Point4.Kripke.preorder_sobocinski];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . suffices ∃ φ, Hilbert.S4Point4 ⊢! φ ∧ ¬FrameClass.S4Point3 ⊧ φ by
      rw [S4Point3.Kripke.connected_preorder];
      tauto;
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

end Logic

end LO.Modal

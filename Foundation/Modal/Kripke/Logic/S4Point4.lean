import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.AxiomPoint4

namespace LO.Modal

open Kripke
open Hilbert.Kripke

abbrev Kripke.FrameClass.preorder_sobocinski : FrameClass := { F | IsPreorder _ F ∧ SatisfiesSobocinskiCondition _ F }

namespace Hilbert.S4Point4.Kripke

instance sound : Sound (Hilbert.S4Point4) Kripke.FrameClass.preorder_sobocinski := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance consistent : Entailment.Consistent (Hilbert.S4Point4) :=
  consistent_of_sound_frameclass FrameClass.preorder_sobocinski $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point4) Kripke.FrameClass.preorder_sobocinski := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point4) Kripke.FrameClass.preorder_sobocinski := inferInstance

end Hilbert.S4Point4.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point4.Kripke.preorder_sobocinski : Logic.S4Point4 = FrameClass.preorder_sobocinski.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.S4Point3 Logic.S4Point4 := ⟨
  by
  constructor;
  . rw [S4Point3.Kripke.connected_preorder, S4Point4.Kripke.preorder_sobocinski];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point4 ⊢! φ ∧ ¬FrameClass.connected_preorder ⊧ φ by
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
      . refine ⟨?_, ⟨?_⟩⟩;
        . tauto;
        . intro x y z; omega;
      . suffices ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M.World) ≺ 1 by
          simpa [Semantics.Realize, Satisfies, M];
        use 2;
        omega;
⟩

end Logic

end LO.Modal

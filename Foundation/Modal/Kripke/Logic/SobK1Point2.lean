import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.AxiomH1
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke

abbrev Kripke.FrameClass.detour_free_preorder : FrameClass := { F | IsPreorder _ F ∧ IsDetourFree _ F }
abbrev Kripke.FrameClass.finite_detour_free_preorder : FrameClass := { F | Finite F ∧ IsPreorder _ F ∧ IsDetourFree _ F }


namespace Hilbert.SobK1Point2.Kripke

instance sound : Sound (Hilbert.SobK1Point2) Kripke.FrameClass.detour_free_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomH1_of_isDetourFree;

instance consistent : Entailment.Consistent (Hilbert.SobK1Point2) :=
  consistent_of_sound_frameclass FrameClass.detour_free_preorder $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.SobK1Point2) Kripke.FrameClass.detour_free_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.SobK1Point2) Kripke.FrameClass.detour_free_preorder := inferInstance

end Hilbert.SobK1Point2.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma SobK1Point2.Kripke.detour_free_preorder : Logic.SobK1Point2 = FrameClass.detour_free_preorder.logic := eq_hilbert_logic_frameClass_logic
lemma SobK1Point2.Kripke.finite_detour_free_preorder : Logic.SobK1Point2 = FrameClass.finite_detour_free_preorder.logic := by sorry

@[simp]
theorem SobK1Point2.proper_extension_of_Grz : Logic.Grz ⊂ Logic.SobK1Point2 := by
  constructor;
  . rw [Grz.Kripke.finite_partial_order, SobK1Point2.Kripke.finite_detour_free_preorder];
    rintro φ hφ F ⟨_, _, _⟩;
    apply hφ;
    refine ⟨inferInstance, { antisymm := ?_ }⟩;
    . intro x y Rxy Ryx;
      have := IsDetourFree.detourFree Rxy Ryx;
      tauto;
  . suffices ∃ φ, Hilbert.SobK1Point2 ⊢! φ ∧ ¬FrameClass.finite_partial_order ⊧ φ by
      rw [Grz.Kripke.finite_partial_order];
      tauto;
    use Axioms.H1 (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x ≤ y⟩, λ w a => w ≠ 1⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩ <;> tauto;
      . suffices ∃ x : M, (0 : M) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 ∧ x = 1 by
          simpa [Semantics.Realize, Satisfies, M];
        use 1;
        constructor;
        . tauto;
        . use 2;
          simp [M];
          omega;

end Logic

end LO.Modal

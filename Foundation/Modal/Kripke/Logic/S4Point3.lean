import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.AxiomPoint3
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Logic.S4Point2
import Foundation.Modal.Kripke.Logic.K4Point3

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.connected_preorder : FrameClass := { F | F.IsPreorder ∧ F.IsPiecewiseStronglyConnected }
abbrev Kripke.FrameClass.finite_connected_preorder : FrameClass := { F | F.IsFinite ∧ F.IsPreorder ∧ F.IsPiecewiseStronglyConnected }

instance {F : Frame} [F.IsPiecewiseStronglyConnected] : F.IsPiecewiseConnected where
instance {F : Frame} [F.IsReflexive] [F.IsPiecewiseStronglyConnected] : F.IsPiecewiseStronglyConvergent where


namespace Hilbert.S4Point3.Kripke

instance sound : Sound (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance consistent : Entailment.Consistent (Hilbert.S4Point3) :=
  consistent_of_sound_frameclass FrameClass.connected_preorder $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.connected_preorder := inferInstance


section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_sound : Sound (Hilbert.S4Point3) Kripke.FrameClass.finite_connected_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance finite_complete : Complete (Hilbert.S4Point3) Kripke.FrameClass.finite_connected_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨_, _⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTransitive)) (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_, ?_⟩;
  . apply isFinite $ by simp;
  . exact isPreorder (preorder := Frame.pointGenerate.isPreorder);
  . exact rooted_isPiecewiseStronglyConnected;
⟩

end FFP

end Hilbert.S4Point3.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point3.Kripke.connected_preorder : Logic.S4Point3 = FrameClass.connected_preorder.logic := eq_hilbert_logic_frameClass_logic
lemma S4Point3.Kripke.finite_connected_preorder : Logic.S4Point3 = FrameClass.finite_connected_preorder.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4Point3.proper_extension_of_S4Point2 : Logic.S4Point2 ⊂ Logic.S4Point3 := by
  constructor;
  . rw [S4Point2.Kripke.confluent_preorder, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬FrameClass.confluent_preorder ⊧ φ by
      rw [S4Point2.Kripke.confluent_preorder];
      tauto;
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . exact axiomPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 4, λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)⟩,
        λ w a => (a = 0 ∧ (w = 1 ∨ w = 3)) ∨ (a = 1 ∧ (w = 2 ∨ w = 3))
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq, M];
        refine ⟨{refl := by omega, trans := by omega;}, {ps_convergent := by intro x y z Rxy Rxz; use 3; omega}⟩;
      . apply Kripke.Satisfies.or_def.not.mpr;
        push_neg;
        constructor;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 1;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;

@[simp]
lemma S4Point3.proper_extension_of_S4 : Logic.S4 ⊂ Logic.S4Point3 := by
  trans Logic.S4Point2;
  . simp;
  . simp;

@[simp]
theorem S4Point3.proper_extension_of_K4Point3 : Logic.K4Point3 ⊂ Logic.S4Point3 := by
  constructor;
  . rw [K4Point3.Kripke.trans_weakConnected, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConnected ⊧ φ by
      rw [K4Point3.Kripke.trans_weakConnected];
      tauto;
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq, M];
        refine ⟨{trans := by omega;}, {p_connected := by simp [M, PiecewiseConnected]; omega }⟩;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;

end Logic

end LO.Modal

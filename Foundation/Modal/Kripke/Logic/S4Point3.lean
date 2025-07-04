import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.AxiomPoint3
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Logic.S4Point2
import Foundation.Modal.Kripke.Logic.K4Point3

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point3 (F : Frame) extends F.IsReflexive, F.IsTransitive, F.IsPiecewiseStronglyConnected
protected class Frame.IsFiniteS4Point3 (F : Frame) extends F.IsFinite, F.IsS4Point3

protected abbrev FrameClass.S4Point3 : FrameClass := { F | F.IsS4Point3 }
protected abbrev FrameClass.finite_S4Point3 : FrameClass := { F | F.IsFiniteS4Point3 }

instance [F.IsS4Point3] : F.IsS4Point2 where
instance [F.IsS4Point3] : F.IsK4Point3 where

protected class Frame.IsLinearPreorder (F : Frame) extends F.IsReflexive, F.IsTransitive, F.IsStronglyConnected
protected class Frame.IsFiniteLinearPreorder (F : Frame) extends F.IsFinite, F.IsLinearPreorder

protected abbrev FrameClass.linearPreorder : FrameClass := { F | F.IsLinearPreorder }
protected abbrev FrameClass.finite_linearPreorder : FrameClass := { F | F.IsFiniteLinearPreorder }

end Kripke


namespace Logic.S4Point3.Kripke

instance sound : Sound Logic.S4Point3 FrameClass.S4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance consistent : Entailment.Consistent Logic.S4Point3 :=
  consistent_of_sound_frameclass FrameClass.S4Point3 $ by
    use whitepoint;
    constructor;

instance canonical : Canonical Logic.S4Point3 FrameClass.S4Point3 := ⟨by constructor⟩

instance complete : Complete Logic.S4Point3 FrameClass.S4Point3 := inferInstance

instance : Complete Logic.S4Point3 { F : Frame | F.IsLinearPreorder } := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.S4Point3);
  intro F hF V r;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply Model.pointGenerate.modal_equivalent_at_root (M := ⟨F, V⟩) (r := r) |>.mp;
  apply hφ;
  exact {}
⟩

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_sound : Sound Logic.S4Point3 FrameClass.finite_S4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance finite_complete : Complete Logic.S4Point3 FrameClass.finite_S4Point3 := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F hF V r;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTransitive)) (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  refine { world_finite := FilterEqvQuotient.finite $ by simp; }
⟩

end FFP

lemma connected_preorder : Logic.S4Point3 = FrameClass.S4Point3.logic := eq_hilbert_logic_frameClass_logic
lemma finite_connected_preorder : Logic.S4Point3 = FrameClass.finite_S4Point3.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4Point2 ⪱ Logic.S4Point3 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, S4Point2.Kripke.confluent_preorder, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point3 ⊢! φ ∧ ¬FrameClass.S4Point2 ⊧ φ by simpa [S4Point2.Kripke.confluent_preorder];
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
      . refine {
          refl := by omega,
          trans := by omega,
          ps_convergent := by intro x y z Rxy Rxz; use 3; omega
        };
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

instance : Logic.S4 ⪱ Logic.S4Point3 := calc
  Logic.S4 ⪱ Logic.S4Point2 := by infer_instance
  _        ⪱ Logic.S4Point3 := by infer_instance

instance : Logic.K4Point3 ⪱ Logic.S4Point3 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, K4Point3.Kripke.trans_weakConnected, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point3 ⊢! φ ∧ ¬FrameClass.IsK4Point3 ⊧ φ by simpa [K4Point3.Kripke.trans_weakConnected];
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
      . refine {
          trans := by omega,
          p_connected := by simp [M, PiecewiseConnected]; omega
        };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;

end Logic.S4Point3.Kripke

end LO.Modal

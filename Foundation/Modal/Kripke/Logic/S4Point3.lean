module

public import Foundation.Modal.Kripke.Logic.S4Point2
public import Foundation.Modal.Kripke.Logic.K4Point3

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

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


instance : Sound Modal.S4Point3 FrameClass.S4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance : Entailment.Consistent Modal.S4Point3 :=
  consistent_of_sound_frameclass FrameClass.S4Point3 $ by
    use whitepoint;
    constructor;

instance : Canonical Modal.S4Point3 FrameClass.S4Point3 := ⟨by constructor⟩

instance : Complete Modal.S4Point3 FrameClass.S4Point3 := inferInstance

instance : Complete Modal.S4Point3 { F : Frame | F.IsLinearPreorder } := ⟨by
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

instance : Sound Modal.S4Point3 FrameClass.finite_S4Point3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance : Complete Modal.S4Point3 FrameClass.finite_S4Point3 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.S4Point3);
  rintro F hF V r;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;
  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  -- TODO: more refactor (auto instantinate)
  have := finestFiltrationTransitiveClosureModel.rooted_isPiecewiseStronglyConnected r (T := φ.subformulas);
  have := finestFiltrationTransitiveClosureModel.isReflexive (M := RM) (T := φ.subformulas);

  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf) (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  refine { world_finite := FilterEqvQuotient.finite $ by simp; }
⟩

end FFP


instance : Modal.S4Point2 ⪱ Modal.S4Point3 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.S4Point2) (FrameClass.S4Point3);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . exact axiomPoint3!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4Point2)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 4, λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)⟩,
        λ a w => (a = 0 ∧ (w = 1 ∨ w = 3)) ∨ (a = 1 ∧ (w = 2 ∨ w = 3))
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
          simp [Satisfies, Semantics.Models, M];
          constructor <;> grind;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          simp [Satisfies, Semantics.Models, M];
          constructor <;> grind;

instance : Modal.S4 ⪱ Modal.S4Point3 := calc
  Modal.S4 ⪱ Modal.S4Point2 := by infer_instance
  _          ⪱ Modal.S4Point3 := by infer_instance

instance : Modal.K4Point3 ⪱ Modal.S4Point3 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.K4Point3) (FrameClass.S4Point3);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomPoint3!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4Point3)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ a w => False
      ⟩;
      use M, 0;
      constructor;
      . refine {
          trans := by omega,
          p_connected := by simp [M, PiecewiseConnected];
        };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Models, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;

instance : Modal.KT ⪱ Modal.S4Point3 := calc
  Modal.KT ⪱ Modal.S4       := by infer_instance
  _        ⪱ Modal.S4Point3 := by infer_instance


end LO.Modal
end

import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4Point2
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4Point2 (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.IsPiecewiseStronglyConvergent where
class Frame.IsFiniteS4Point2 (F : Frame) extends F.IsFinite, F.IsReflexive, F.IsTransitive, F.IsPiecewiseStronglyConvergent

instance [F.IsS4Point2] : F.IsS4 where
instance [F.IsS4Point2] : F.IsK4Point2 where

abbrev FrameClass.S4Point2 : FrameClass := { F | F.IsS4Point2  }
abbrev FrameClass.finite_S4Point2 : FrameClass := { F | F.IsFiniteS4Point2 }

end Kripke


instance : Sound Modal.S4Point2 FrameClass.S4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance : Entailment.Consistent Modal.S4Point2 :=
  consistent_of_sound_frameclass FrameClass.S4Point2 $ by
    use whitepoint;
    constructor;

instance : Canonical Modal.S4Point2 FrameClass.S4Point2 := ⟨by constructor⟩

instance : Complete Modal.S4Point2 FrameClass.S4Point2 := inferInstance


section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance : Sound Modal.S4Point2 FrameClass.finite_S4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance : Complete Modal.S4Point2 FrameClass.finite_S4Point2 := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.S4Point2);
  rintro F hF V r;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel (M↾r) (φ.subformulas);
  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTransitive)) (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  exact {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
  }
  /-

  refine ⟨?_, ?_, ?_⟩;
  . apply isFinite $ by simp;
  . exact finestFiltrationTransitiveClosureModel.isPreorder (preorder := Frame.pointGenerate.isPreorder);
  . exact finestFiltrationTransitiveClosureModel.rooted_isPiecewiseStronglyConvergent;
  -/
⟩

end FFP


instance : Modal.S4 ⪱ Modal.S4Point2 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Point2 (.atom 0)
    constructor;
    . exact axiomPoint2!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.S4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = y) ⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq]; refine { refl := by omega, trans := by omega; };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, x ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Models, Satisfies];
        use 1;
        refine ⟨by omega, ?_, ?_⟩;
        . intro y;
          match y with
          | 0 => omega;
          | 1 => tauto;
          | 2 => omega;
        . use 2;
          constructor;
          . omega;
          . omega;

instance : Modal.K4Point2 ⪱ Modal.S4Point2 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass (FrameClass.K4Point2) (FrameClass.S4Point2);
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Point2 (.atom 0));
    constructor;
    . exact axiomPoint2!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K4Point2)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine { p_convergent := by simp [M, PiecewiseConvergent ]; omega; };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x by
          simpa [M, Semantics.Models, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . omega;
        . use 1; omega;

instance : Modal.KT ⪱ Modal.S4Point2 := calc
  Modal.KT ⪱ Modal.S4       := by infer_instance
  _        ⪱ Modal.S4Point2 := by infer_instance

end LO.Modal

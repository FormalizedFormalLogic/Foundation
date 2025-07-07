import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4Point2
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4Point2 (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.IsPiecewiseStronglyConvergent where
class Frame.IsFiniteS4Point2 (F : Frame) extends F.IsFinite, F.IsReflexive, F.IsTransitive, F.IsPiecewiseStronglyConvergent

instance [F.IsS4Point2] : F.IsS4 where
instance [F.IsS4Point2] : F.IsK4Point2 where

abbrev FrameClass.S4Point2 : FrameClass := { F | F.IsS4Point2  }
abbrev FrameClass.finite_S4Point2 : FrameClass := { F | F.IsFiniteS4Point2 }

end Kripke



namespace Logic.S4Point2.Kripke

instance : Sound Logic.S4Point2 FrameClass.S4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance : Entailment.Consistent Logic.S4Point2 :=
  consistent_of_sound_frameclass FrameClass.S4Point2 $ by
    use whitepoint;
    constructor;

instance : Canonical Logic.S4Point2 FrameClass.S4Point2 := ⟨by constructor⟩

instance : Complete Logic.S4Point2 FrameClass.S4Point2 := inferInstance


section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_sound : Sound Logic.S4Point2 FrameClass.finite_S4Point2 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance finite_complete : Complete Logic.S4Point2 FrameClass.finite_S4Point2 := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
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

protected lemma confluent_preorder : Logic.S4Point2 = FrameClass.S4Point2.logic := eq_hilbert_logic_frameClass_logic
protected lemma finite_confluent_preorder : Logic.S4Point2 = FrameClass.finite_S4Point2.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4 ⪱ Logic.S4Point2 := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point2 ⊢! φ ∧ ¬FrameClass.S4 ⊧ φ by simpa [S4.Kripke.preorder];
    use Axioms.Point2 (.atom 0)
    constructor;
    . exact axiomPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = y) ⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq]; refine { refl := by omega, trans := by omega; };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, x ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
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

instance : Logic.K4Point2 ⪱ Logic.S4Point2 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, K4Point2.Kripke.K4Point2, S4Point2.Kripke.confluent_preorder];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point2 ⊢! φ ∧ ¬Kripke.FrameClass.K4Point2 ⊧ φ by simpa [K4Point2.Kripke.K4Point2];
    use (Axioms.Point2 (.atom 0));
    constructor;
    . exact axiomPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine { p_convergent := by simp [M, PiecewiseConvergent ]; omega; };
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . omega;
        . use 1; omega;

end Logic.S4Point2.Kripke

end LO.Modal

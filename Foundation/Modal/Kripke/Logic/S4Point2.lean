import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Filtration
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.K4Point2
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.confluent_preorder : FrameClass := { F | F.IsPreorder ∧ F.IsPiecewiseStronglyConvergent  }
abbrev Kripke.FrameClass.finite_confluent_preorder : FrameClass := { F | F.IsFinite ∧ F.IsPreorder ∧ F.IsPiecewiseStronglyConvergent }

instance {F : Kripke.Frame} [F.IsPiecewiseStronglyConvergent] : F.IsPiecewiseConvergent where


namespace Hilbert.S4Point2.Kripke

instance sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent (Hilbert.S4Point2) :=
  consistent_of_sound_frameclass FrameClass.confluent_preorder $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ?_⟩;
  . constructor;
  . infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := inferInstance


section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomPoint2_of_confluent;

instance finite_complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.finite_confluent_preorder := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F ⟨_, _⟩ V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel (M↾r) (φ.subformulas);
  apply filtration FRM (finestFiltrationTransitiveClosureModel.filterOf (trans := Frame.pointGenerate.isTransitive)) (by subformula) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_, ?_⟩;
  . apply isFinite $ by simp;
  . exact finestFiltrationTransitiveClosureModel.isPreorder (preorder := Frame.pointGenerate.isPreorder);
  . exact finestFiltrationTransitiveClosureModel.rooted_isPiecewiseStronglyConvergent;
⟩

end FFP

end Hilbert.S4Point2.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point2.Kripke.confluent_preorder : Logic.S4Point2 = FrameClass.confluent_preorder.logic := eq_hilbert_logic_frameClass_logic
lemma S4Point2.Kripke.finite_confluent_preorder : Logic.S4Point2 = FrameClass.finite_confluent_preorder.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4Point2.proper_extension_of_S4 : Logic.S4 ⊂ Logic.S4Point2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
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

@[simp]
theorem S4Point2.proper_extension_of_K4Point2 : Logic.K4Point2 ⊂ Logic.S4Point2 := by
  constructor;
  . rw [K4Point2.Kripke.trans_weakConfluent, S4Point2.Kripke.confluent_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConfluent ⊧ φ by
      rw [K4Point2.Kripke.trans_weakConfluent];
      tauto;
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
        refine ⟨{}, { p_convergent := by simp [M, PiecewiseConvergent ]; omega; }⟩;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . omega;
        . use 1; omega;

end Logic

end LO.Modal

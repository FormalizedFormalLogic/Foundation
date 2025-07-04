import Foundation.Modal.Kripke.Logic.K4Point3
import Foundation.Modal.Kripke.Logic.K5

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsK45 (F : Kripke.Frame) extends F.IsTransitive, F.IsEuclidean

protected abbrev FrameClass.IsK45 : FrameClass := { F | F.IsK45 }

instance {F : Kripke.Frame} [F.IsK45] : F.IsK4Point3 where

end Kripke


namespace Logic.K45.Kripke

instance sound : Sound Logic.K45 FrameClass.IsK45 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent Logic.K45 := consistent_of_sound_frameclass FrameClass.IsK45 $ by
  use whitepoint;
  constructor;


instance canonical : Canonical Logic.K45 FrameClass.IsK45 := ⟨by constructor⟩

instance complete : Complete Logic.K45 FrameClass.IsK45 := inferInstance

lemma trans_eucl : Logic.K45 = FrameClass.IsK45.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.K5 ⪱ Logic.K45 := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms $ by rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K45 ⊢! φ ∧ ¬Kripke.FrameClass.K5 ⊧ φ by simpa [K5.Kripke.eucl];
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        exact { reucl := by simp [RightEuclidean]; omega }
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ z, x ≺ z ∧ ¬z = 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y; tauto;
        . exact ⟨1, by omega, 2, by omega, by trivial⟩;

instance : Logic.K4Point3 ⪱ Logic.K45 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, K4Point3.Kripke.trans_weakConnected, K45.Kripke.trans_eucl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.K45 ⊢! φ ∧ ¬FrameClass.IsK4Point3 ⊧ φ by simpa [K4Point3.Kripke.trans_weakConnected];
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x < y⟩,
        λ w a => w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine {
          trans := by omega,
          p_connected := by simp [PiecewiseConnected, M]; omega;
        };
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          omega;

end Logic.K45.Kripke

end LO.Modal

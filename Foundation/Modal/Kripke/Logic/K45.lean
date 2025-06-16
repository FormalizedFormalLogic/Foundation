import Foundation.Modal.Kripke.Logic.K4Point3
import Foundation.Modal.Kripke.Logic.K5

namespace LO.Modal

open Kripke
open Hilbert.Kripke

protected abbrev Kripke.FrameClass.trans_eucl : FrameClass := { F | F.IsTransitive ∧ F.IsEuclidean }

namespace Hilbert.K45.Kripke

instance sound : Sound (Hilbert.K45) FrameClass.trans_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.K45) := consistent_of_sound_frameclass Kripke.FrameClass.trans_eucl $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.K45) FrameClass.trans_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.K45) FrameClass.trans_eucl := inferInstance

end Hilbert.K45.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma K45.Kripke.trans_eucl : Logic.K45 = FrameClass.trans_eucl.logic := eq_hilbert_logic_frameClass_logic

theorem K45.proper_extension_of_K : Logic.K5 ⊂ Logic.K45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬Kripke.FrameClass.eucl ⊧ φ by
      rw [K5.Kripke.eucl];
      tauto;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
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

theorem K5.proper_extension_of_K4Point3 : Logic.K4Point3 ⊂ Logic.K45 := by
  constructor;
  . rw [K4Point3.Kripke.trans_weakConnected, K45.Kripke.trans_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConnected ⊧ φ by
      rw [K4Point3.Kripke.trans_weakConnected];
      tauto;
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
      . simp;
        refine ⟨{ trans := by omega }, { p_connected := by simp [PiecewiseConnected, M]; omega}⟩;
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          omega;

end Logic

end LO.Modal

import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Logic.KTB
import Foundation.Modal.Kripke.Logic.KD45
import Foundation.Modal.Kripke.Logic.KB4
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.S4Point3

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

protected abbrev FrameClass.refl_eucl : FrameClass := { F | IsRefl _ F ∧ IsEuclidean _ F }

protected abbrev FrameClass.universal : FrameClass := { F | IsUniversal _ F }

protected abbrev FrameClass.finite_refl_eucl: FrameClass := { F | F.IsFinite ∧ IsRefl _ F ∧ IsEuclidean _ F }

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ Kripke.FrameClass.refl_eucl ⊧ φ := by
  constructor;
  . rintro h F ⟨F_refl, F_eucl⟩ V r;
    apply @Model.pointGenerate.modal_equivalent_at_root _ _ |>.mp;
    apply h;
    apply Set.mem_setOf_eq.mpr;
    exact Frame.pointGenerate.isUniversal (r := r) (refl := F_refl) (eucl := F_eucl);
  . rintro h F F_univ;
    replace F_univ := Set.mem_setOf_eq.mp F_univ
    apply h;
    constructor <;> infer_instance;

end Kripke


namespace Hilbert.S5.Kripke

instance sound_refl_eucl : Sound (Hilbert.S5) Kripke.FrameClass.refl_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFive_of_euclidean;

instance sound_universal : Sound (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact sound_refl_eucl.sound hF;
⟩

instance consistent : Entailment.Consistent (Hilbert.S5) := consistent_of_sound_frameclass Kripke.FrameClass.refl_eucl $ by
  use whitepoint;
  refine ⟨inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S5) Kripke.FrameClass.refl_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete_refl_eucl : Complete (Hilbert.S5) Kripke.FrameClass.refl_eucl := inferInstance

instance complete_universal : Complete (Hilbert.S5) FrameClass.universal := ⟨by
  intro φ hF;
  apply Kripke.complete_refl_eucl.complete;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mp;
  exact hF;
⟩

end Hilbert.S5.Kripke


namespace Logic

open Formula
open Entailment
open Kripke

lemma S5.Kripke.refl_eucl : Logic.S5 = FrameClass.refl_eucl.logic := eq_hilbert_logic_frameClass_logic
lemma S5.Kripke.universal : Logic.S5 = FrameClass.universal.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.KTB Logic.S5 := ⟨by
  constructor;
  . rw [KTB.Kripke.refl_symm, S5.Kripke.refl_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬Kripke.FrameClass.refl_symm ⊧ φ by
      rw [KTB.Kripke.refl_symm];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = 1 ∧ y ≠ 2) ∨ (x = 2 ∧ y ≠ 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by omega⟩, ⟨by omega⟩⟩;
      . suffices (0 : M.World) ≺ 1 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          constructor <;> omega;
⟩

instance : ProperSublogic Logic.KD45 Logic.S5 := ⟨by
  constructor;
  . rw [KD45.Kripke.serial_trans_eucl, S5.Kripke.refl_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.serial_trans_eucl ⊧ φ by
      rw [KD45.Kripke.serial_trans_eucl];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨?_⟩, ⟨by omega⟩, ⟨by unfold Euclidean; omega⟩⟩;
        . intro x;
          match x with
          | 0 => use 1; tauto;
          | 1 => use 1; tauto;
      . simp [Semantics.Realize, Satisfies, M];
        tauto;
⟩

instance : ProperSublogic Logic.KB4 Logic.S5 := ⟨by
  constructor;
  . rw [KB4.Kripke.refl_trans, S5.Kripke.refl_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.symm_trans ⊧ φ by
      rw [KB4.Kripke.refl_trans];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ x _ => False⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by tauto⟩⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

instance : ProperSublogic Logic.S4 Logic.S5 := ⟨by
  constructor;
  . rw [S4.Kripke.preorder, S5.Kripke.refl_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬Kripke.FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w _ => w = 2)⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        apply isPreorder_iff _ _ |>.mpr;
        refine ⟨⟨by tauto⟩, ⟨by omega⟩⟩
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          omega;
⟩

instance : ProperSublogic Logic.S4Point3 Logic.S5 := ⟨by
  constructor;
  . rw [S4Point3.Kripke.connected_preorder, S5.Kripke.universal];
    rintro φ hφ F F_univ;
    apply hφ;
    replace F_univ := Set.mem_setOf_eq.mp F_univ
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.connected_preorder ⊧ φ by
      rw [S4Point3.Kripke.connected_preorder];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w a => (w = 0)⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        refine ⟨?_, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨by omega⟩, ⟨by omega⟩⟩;
        . rintro x y z ⟨Rxy, Ryz⟩; omega;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;
⟩

end Logic

end LO.Modal

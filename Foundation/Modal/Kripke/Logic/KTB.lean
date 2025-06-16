import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KDB
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKTB (F : Kripke.Frame) extends F.IsReflexive, F.IsSymmetric
protected class Frame.IsFiniteKTB (F : Kripke.Frame) extends F.IsFinite, F.IsKTB

protected abbrev FrameClass.KTB : FrameClass := { F | F.IsKTB }
protected abbrev FrameClass.finite_KTB: FrameClass := { F | F.IsFiniteKTB }

end Kripke


namespace Hilbert.KTB.Kripke

instance sound : Sound (Hilbert.KTB) FrameClass.KTB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KTB) := consistent_of_sound_frameclass
  FrameClass.KTB $ by
    use whitepoint;
    constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KTB) FrameClass.KTB :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KTB) FrameClass.KTB := inferInstance

instance finite_complete : Complete (Hilbert.KTB) FrameClass.finite_KTB := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F hF V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationModel M φ.subformulas;
  apply filtration FM (finestFiltrationModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  apply Set.mem_setOf_eq.mpr;
  sorry;
  /-
  apply Frame.isFiniteKTB_iff _ |>.mpr;
  constructor;
  . apply finestFiltrationModel.isFinite $ by simp;
  . constructor;
    . apply finestFiltrationModel.isReflexive; simp;
    . sorry;
  -/

  -- have : FM.IsFinite := finestFiltrationModel.isFinite $ by simp;
  -- have : FM.IsReflexive := by sorry; -- apply finestFiltrationModel.isReflexive; simp;
  -- have : FM.IsSymmetric := by sorry; -- apply finestFiltrationModel.isSymmetric; simp;
  -- infer_instance
⟩

end Hilbert.KTB.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KTB.Kripke.refl_symm : Logic.KTB = FrameClass.KTB.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem KTB.proper_extension_of_KT : Logic.KT ⊂ Logic.KTB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬Kripke.FrameClass.KT ⊧ φ by
      rw [KT.Kripke.refl];
      tauto;
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        omega;

@[simp]
theorem KTB.proper_extension_of_KDB : Logic.KDB ⊂ Logic.KTB := by
  constructor;
  . rw [KDB.Kripke.serial_symm, KTB.Kripke.refl_symm];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬FrameClass.serial_symm ⊧ φ by
      rw [KDB.Kripke.serial_symm];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≠ y⟩, λ x _ => x = 1⟩, 0;
      constructor;
      . refine ⟨
          { serial := by
              intro x;
              match x with
              | 0 => use 1; omega;
              | 1 => use 0; omega;
          },
          { symm := by simp; omega }
        ⟩;
      . simp [Semantics.Realize, Satisfies];
        omega;

end Logic

end LO.Modal

import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KDB
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsKTB (F : Kripke.Frame) extends F.IsReflexive, F.IsSymmetric
protected class Frame.IsFiniteKTB (F : Kripke.Frame) extends F.IsFinite, F.IsKTB

instance [F.IsKTB] : F.IsKDB where

protected abbrev FrameClass.KTB : FrameClass := { F | F.IsKTB }
protected abbrev FrameClass.finite_KTB: FrameClass := { F | F.IsFiniteKTB }

end Kripke


namespace Logic.KTB.Kripke

instance sound : Sound Logic.KTB FrameClass.KTB := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent Logic.KTB := consistent_of_sound_frameclass FrameClass.KTB $ by
  use whitepoint;
  constructor;


instance canonical : Canonical Logic.KTB FrameClass.KTB := ⟨by constructor⟩

instance complete : Complete Logic.KTB FrameClass.KTB := inferInstance

instance finite_complete : Complete Logic.KTB FrameClass.finite_KTB := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationModel M φ.subformulas;
  apply filtration FM (finestFiltrationModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  apply Set.mem_setOf_eq.mpr;
  refine {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    refl := finestFiltrationModel.isReflexive.refl
    symm := finestFiltrationModel.isSymmetric.symm
  }
⟩

lemma refl_symm : Logic.KTB = FrameClass.KTB.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.KT ⪱ Logic.KTB := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KTB ⊢! φ ∧ ¬Kripke.FrameClass.KT ⊧ φ by simpa [KT.Kripke.refl];
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

instance : Logic.KDB ⪱ Logic.KTB := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    simp only [iff_provable, Set.mem_setOf_eq, KDB.Kripke.serial_symm, KTB.Kripke.refl_symm];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.KTB ⊢! φ ∧ ¬Kripke.FrameClass.KDB ⊧ φ by simpa [KDB.Kripke.serial_symm];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≠ y⟩, λ x _ => x = 1⟩, 0;
      constructor;
      . refine {
          serial := by
            intro x;
            match x with
            | 0 => use 1; omega;
            | 1 => use 0; omega;
          symm := by simp; omega
        };
      . simp [Semantics.Realize, Satisfies];
        omega;

end Logic.KTB.Kripke

end LO.Modal

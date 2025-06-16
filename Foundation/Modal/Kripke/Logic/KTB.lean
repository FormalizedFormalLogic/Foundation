import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KDB
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.refl_symm : FrameClass := { F | F.IsReflexive ∧ F.IsSymmetric }

abbrev Kripke.FrameClass.finite_refl_symm: FrameClass := { F | Finite F.World ∧ F.IsReflexive ∧ F.IsSymmetric }

namespace Hilbert.KTB.Kripke

instance sound : Sound (Hilbert.KTB) Kripke.FrameClass.refl_symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KTB) := consistent_of_sound_frameclass
  Kripke.FrameClass.refl_symm $ by
    use whitepoint;
    constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KTB) Kripke.FrameClass.refl_symm :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KTB) Kripke.FrameClass.refl_symm := inferInstance

instance finite_complete : Complete (Hilbert.KTB) Kripke.FrameClass.finite_refl_symm := ⟨by
  intro φ hp;
  apply Kripke.complete.complete;
  intro F ⟨F_refl, F_symm⟩ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationModel M φ.subformulas;
  apply filtration FM (finestFiltrationModel.filterOf) (by subformula) |>.mpr;
  apply hp;
  refine ⟨?_, ?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . apply Kripke.finestFiltrationModel.isReflexive;
  . apply Kripke.finestFiltrationModel.isSymmetric;
⟩

end Hilbert.KTB.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KTB.Kripke.refl_symm : Logic.KTB = FrameClass.refl_symm.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem KTB.proper_extension_of_KT : Logic.KT ⊂ Logic.KTB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬Kripke.FrameClass.refl ⊧ φ by
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
      use ⟨⟨Bool, λ x y => x ≠ y⟩, λ x _ => x = true⟩, false;
      constructor;
      . refine ⟨{ serial := by simp [Serial] }, { symm := by simp }⟩;
      . simp [Semantics.Realize, Satisfies];
        tauto;

end Logic

end LO.Modal

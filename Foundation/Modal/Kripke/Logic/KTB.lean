import Foundation.Modal.Kripke.Logic.KT
import Foundation.Modal.Kripke.Logic.KDB
import Foundation.Modal.Kripke.Filtration

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsKTB (F : Kripke.Frame) extends F.IsReflexive, F.IsSymmetric
protected class Frame.IsFiniteKTB (F : Kripke.Frame) extends F.IsFinite, F.IsKTB

instance [F.IsKTB] : F.IsKDB where

protected abbrev FrameClass.KTB : FrameClass := { F | F.IsKTB }
protected abbrev FrameClass.finite_KTB: FrameClass := { F | F.IsFiniteKTB }

end Kripke


instance : Sound Modal.KTB FrameClass.KTB := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomB_of_symmetric;

instance : Entailment.Consistent Modal.KTB := consistent_of_sound_frameclass FrameClass.KTB $ by
  use whitepoint;
  constructor;

instance : Canonical Modal.KTB FrameClass.KTB := ⟨by constructor⟩

instance : Complete Modal.KTB FrameClass.finite_KTB := ⟨by
  intro φ hp;
  apply Complete.complete (𝓜 := FrameClass.KTB);
  intro F hF V x;
  replace hF := Set.mem_setOf_eq.mp hF;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFiltrationModel M φ.subformulas;
  apply filtration FM (finestFiltrationModel.filterOf) (by simp) |>.mpr;
  apply hp;
  apply Set.mem_setOf_eq.mpr;
  refine {
    world_finite := by apply FilterEqvQuotient.finite $ by simp;
    refl := finestFiltrationModel.isReflexive.refl
    symm := finestFiltrationModel.isSymmetric.symm
  }
⟩

instance : Modal.KT ⪱ Modal.KTB := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KT);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Models, Satisfies];
        use 1;
        omega;

instance : Modal.KDB ⪱ Modal.KTB := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.KDB FrameClass.KTB;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KDB);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
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
      . simp [Semantics.Models, Satisfies];
        omega;


end LO.Modal

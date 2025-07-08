import Foundation.Modal.Kripke.Rooted
import Foundation.Modal.Kripke.Logic.KTB
import Foundation.Modal.Kripke.Logic.KD45
import Foundation.Modal.Kripke.Logic.KB4
import Foundation.Modal.Kripke.Logic.S4
import Foundation.Modal.Kripke.Logic.S4Point4
import Foundation.Vorspiel.HRel.Universal

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Frame}

class Frame.IsUniversal (F : Frame) extends _root_.IsUniversal F.Rel
@[simp] lemma universal [F.IsUniversal] : ∀ {x y : F.World}, x ≺ y := by apply IsUniversal.universal;

instance [F.IsUniversal] : F.IsEuclidean := by simp
instance [F.IsUniversal] : F.IsPreorder where

protected class Frame.IsS5 (F : Frame) extends F.IsReflexive, F.IsEuclidean
protected class Frame.IsFiniteS5 (F : Frame) extends F.IsFinite, F.IsS5

instance [F.IsS5] : F.IsKD45 where
instance [F.IsS5] : F.IsKB4 where
instance [F.IsS5] : F.IsKTB where
instance [F.IsS5] : F.IsS4Point4 where

protected abbrev FrameClass.S5 : FrameClass := { F | F.IsS5 }
protected abbrev FrameClass.finite_S5: FrameClass := { F | F.IsFiniteS5 }
protected abbrev FrameClass.universal : FrameClass := { F | F.IsUniversal }

instance Frame.pointGenerate.isUniversal (F : Frame) (r : F.World) (_ : F.IsS5) : (F↾r).IsUniversal where
  universal := by
    rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
    . simp;
    . exact hy.unwrap;
    . suffices x ≺ y by simpa;
      exact IsSymm.symm _ _ hx.unwrap;
    . suffices x ≺ y by simpa;
      apply F.eucl hx.unwrap hy.unwrap ;

lemma iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass : FrameClass.universal ⊧ φ ↔ FrameClass.S5 ⊧ φ := by
  constructor;
  . rintro h F hF V r;
    apply @Model.pointGenerate.modal_equivalent_at_root _ _ |>.mp;
    apply h;
    apply Frame.pointGenerate.isUniversal F r hF;
  . rintro h F F_univ;
    apply h;
    simp_all;
    constructor;

end Kripke


namespace Hilbert.S5.Kripke

instance sound_refl_eucl : Sound Hilbert.S5 FrameClass.S5 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFive_of_euclidean;

instance sound_universal : Sound Hilbert.S5 FrameClass.universal := ⟨by
  intro φ hF;
  apply iff_validOnUniversalFrameClass_validOnReflexiveEuclideanFrameClass.mpr;
  exact sound_refl_eucl.sound hF;
⟩

instance : Entailment.Consistent Hilbert.S5 := consistent_of_sound_frameclass FrameClass.S5 $ by
  use whitepoint;
  constructor;

instance : Canonical Hilbert.S5 FrameClass.S5 := ⟨by constructor⟩

instance complete_refl_eucl : Complete Hilbert.S5 FrameClass.S5 := inferInstance

instance complete_universal : Complete Hilbert.S5 FrameClass.universal := ⟨by
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

lemma S5.Kripke.refl_eucl : Modal.S5 = FrameClass.S5.logic := eq_hilbert_logic_frameClass_logic
lemma S5.Kripke.universal : Modal.S5 = FrameClass.universal.logic := eq_hilbert_logic_frameClass_logic

instance : Hilbert.KTB ⪱ Hilbert.S5 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.KTB ⊧ φ → FrameClass.S5 ⊧ φ by
      simpa [KTB.Kripke.refl_symm, S5.Kripke.refl_eucl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.KTB ⊧ φ by simpa [KTB.Kripke.refl_symm];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = 1 ∧ y ≠ 2) ∨ (x = 2 ∧ y ≠ 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine { refl := by omega, symm := by omega };
      . suffices (0 : M.World) ≺ 1 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          constructor <;> omega;

instance : Hilbert.KD45 ⪱ Hilbert.S5 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.serial_trans_eucl ⊧ φ → FrameClass.S5 ⊧ φ by
      simpa [KD45.Kripke.serial_trans_eucl, S5.Kripke.refl_eucl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.serial_trans_eucl ⊧ φ by simpa [KD45.Kripke.serial_trans_eucl];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine {
          serial := by intro x; use 1; omega;,
          trans := by omega,
          reucl := by simp [RightEuclidean]; omega
        }
      . simp [Semantics.Realize, Satisfies, M];
        tauto;

instance : Hilbert.KB4 ⪱ Hilbert.S5 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.KB4 ⊧ φ → FrameClass.S5 ⊧ φ by
      simpa [KB4.Kripke.refl_trans, S5.Kripke.refl_eucl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.KB4 ⊧ φ by simpa [KB4.Kripke.refl_trans];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ x _ => False⟩, 0;
      constructor;
      . refine { symm := by tauto, trans := by tauto };
      . simp [Semantics.Realize, Satisfies];

instance : Hilbert.S4Point4 ⪱ Hilbert.S5 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.S4Point4 ⊧ φ → FrameClass.S5 ⊧ φ by
      simpa [S4Point4.Kripke.preorder_sobocinski, S5.Kripke.refl_eucl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬Kripke.FrameClass.S4Point4 ⊧ φ by simpa [S4Point4.Kripke.preorder_sobocinski];
    use Axioms.Five (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w a => w = 0⟩;
      use M, 0;
      constructor;
      . refine {
          sobocinski := by
            intro x y z _ _;
            match x, y with
            | 0, 0 => contradiction;
            | 0, 1 => omega;
            | 1, 0 => contradiction;
            | 1, 1 => contradiction;
        };
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x : M.World, (0 : M) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

instance : Hilbert.S4 ⪱ Hilbert.S5 := calc
  Hilbert.S4 ⪱ Hilbert.S4Point2 := by infer_instance
  _          ⪱ Hilbert.S4Point3 := by infer_instance
  _          ⪱ Hilbert.S4Point4 := by infer_instance
  _          ⪱ Hilbert.S5       := by infer_instance

end Logic

instance : Modal.KTB ⪱ Modal.S5 := inferInstance

instance : Modal.KD45 ⪱ Modal.S5 := inferInstance

instance : Modal.KB4 ⪱ Modal.S5 := inferInstance

instance : Modal.S4Point4 ⪱ Modal.S5 := inferInstance

instance : Modal.S4 ⪱ Modal.S5 := inferInstance

end LO.Modal

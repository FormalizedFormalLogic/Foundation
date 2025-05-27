import Foundation.Modal.Kripke.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.Hilbert.K45
import Foundation.Modal.Kripke.Hilbert.K5
import Foundation.Modal.Kripke.Hilbert.KB
import Foundation.Modal.Kripke.Hilbert.KB4
import Foundation.Modal.Kripke.Hilbert.KB4
import Foundation.Modal.Kripke.Hilbert.KD
import Foundation.Modal.Kripke.Hilbert.KD4
import Foundation.Modal.Kripke.Hilbert.KD5
import Foundation.Modal.Kripke.Hilbert.KD45
import Foundation.Modal.Kripke.Hilbert.KDB
import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KT4B
import Foundation.Modal.Kripke.Hilbert.KTB
import Foundation.Modal.Kripke.Hilbert.KTB
import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.Hilbert.S5
import Foundation.Modal.Entailment.KT

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem KTB_ssubset_S5 : Logic.KTB ⊂ Logic.S5 := by
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
instance : ProperSublogic Logic.KTB Logic.S5 := ⟨KTB_ssubset_S5⟩

theorem KD45_ssubset_S5 : Logic.KD45 ⊂ Logic.S5 := by
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
instance : ProperSublogic Logic.KD45 Logic.S5 := ⟨KD45_ssubset_S5⟩

theorem KB4_ssubset_S5 : Logic.KB4 ⊂ Logic.S5 := by
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
instance : ProperSublogic Logic.KB4 Logic.S5 := ⟨KB4_ssubset_S5⟩

theorem KT_ssubset_KTB : Logic.KT ⊂ Logic.KTB := by
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
instance : ProperSublogic Logic.KT Logic.KTB := ⟨KT_ssubset_KTB⟩

theorem KDB_ssubset_KTB : Logic.KDB ⊂ Logic.KTB := by
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
      . refine ⟨⟨?_⟩, ⟨by tauto⟩⟩;
        . intro x;
          use !x;
          simp;
      . simp [Semantics.Realize, Satisfies];
        tauto;
instance : ProperSublogic Logic.KDB Logic.KTB := ⟨KDB_ssubset_KTB⟩

theorem KT_ssubset_S4 : Logic.KT ⊂ Logic.S4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomT!]) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬Kripke.FrameClass.refl ⊧ φ by
      rw [KT.Kripke.refl];
      tauto;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => (x = 0 ∧ y ≠ 2) ∨ (x = 1 ∧ y ≠ 0) ∨ (x = 2 ∧ y = 2)⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨by omega⟩;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y hy;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => omega;
        . use 1;
          constructor;
          . omega;
          . use 2;
            refine ⟨by omega;, by trivial, by trivial⟩;
instance : ProperSublogic Logic.KT Logic.S4 := ⟨KT_ssubset_S4⟩

theorem KD4_ssubset_S4 : Logic.KD4 ⊂ Logic.S4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬FrameClass.serial_trans ⊧ φ by
      rw [KD4.Kripke.serial_trans];
      tauto;
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by omega⟩⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KD4 Logic.S4 := ⟨KD4_ssubset_S4⟩

theorem KD4_ssubset_KD45 : Logic.KD4 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.serial_trans ⊧ φ by
      rw [KD4.Kripke.serial_trans];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => x = y ∨ x < y⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by omega⟩⟩;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.KD4 Logic.KD45 := ⟨KD4_ssubset_KD45⟩

theorem KD5_ssubset_KD45 : Logic.KD5 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.serial_eucl ⊧ φ by
      rw [KD5.Kripke.serial_eucl];
      tauto;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨?_⟩, ⟨by unfold Euclidean; omega⟩⟩;
        . intro x;
          match x with
          | 0 => use 1; tauto;
          | 1 => use 1; omega;
          | 2 => use 2; omega;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            constructor;
            . omega;
            . trivial;
instance : ProperSublogic Logic.KD5 Logic.KD45 := ⟨KD5_ssubset_KD45⟩

theorem K45_ssubset_KD45 : Logic.K45 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.trans_eucl ⊧ φ by
      rw [K45.Kripke.trans_eucl];
      tauto;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => True⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by tauto⟩⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K45 Logic.KD45 := ⟨K45_ssubset_KD45⟩

theorem K45_ssubset_KB4 : Logic.K45 ⊂ Logic.KB4 := by
  constructor;
  . rw [K45.Kripke.trans_eucl, KB4.Kripke.refl_trans];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬FrameClass.trans_eucl ⊧ φ by
      rw [K45.Kripke.trans_eucl];
      tauto;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by tauto⟩⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K45 Logic.KB4 := ⟨K45_ssubset_KB4⟩

theorem KB_ssubset_KB4 : Logic.KB ⊂ Logic.KB4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬FrameClass.symm ⊧ φ by
      rw [KB.Kripke.symm];
      tauto;
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . refine ⟨by simp⟩;
      . simp [Semantics.Realize, Satisfies];
        tauto;
instance : ProperSublogic Logic.KB Logic.KB4 := ⟨KB_ssubset_KB4⟩

theorem KD_ssubset_KT : Logic.KD ⊂ Logic.KT := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomD!]) |>.subset;
  . suffices ∃ φ, Hilbert.KT ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KD Logic.KT := ⟨KD_ssubset_KT⟩


theorem KD_ssubset_KDB : Logic.KD ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine ⟨?_⟩;
        intro x;
        match x with
        | 0 => use 1; tauto;
        | 1 => use 1;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor <;> omega;
instance : ProperSublogic Logic.KD Logic.KDB := ⟨KD_ssubset_KDB⟩

theorem KB_ssubset_KDB : Logic.KB ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬FrameClass.symm ⊧ φ by
      rw [KB.Kripke.symm];
      tauto;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KB Logic.KDB := ⟨KB_ssubset_KDB⟩

theorem KD_ssubset_KD4 : Logic.KD ⊂ Logic.KD4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩, false;
      constructor;
      . refine ⟨by simp [Serial]⟩;
      . simp [Semantics.Realize, Satisfies];
        tauto;
instance : ProperSublogic Logic.KD Logic.KD4 := ⟨KD_ssubset_KD4⟩

theorem K4_ssubset_KD4 : Logic.K4 ⊂ Logic.KD4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K4 Logic.KD4 := ⟨K4_ssubset_KD4⟩

lemma K4_ssubset_S4 : Logic.K4 ⊂ Logic.S4 := by
  trans;
  . exact K4_ssubset_KD4
  . exact KD4_ssubset_S4

theorem KD_ssubset_KD5 : Logic.KD ⊂ Logic.KD5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬FrameClass.serial ⊧ φ by
      rw [KD.Kripke.serial];
      tauto;
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> tauto;
instance : ProperSublogic Logic.KD Logic.KD5 := ⟨KD_ssubset_KD5⟩

theorem K5_ssubset_KD5 : Logic.K5 ⊂ Logic.KD5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬Kripke.FrameClass.eucl ⊧ φ by
      rw [K5.Kripke.eucl];
      tauto;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . refine ⟨by tauto⟩
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K5 Logic.KD5 := ⟨K5_ssubset_KD5⟩

theorem K4_ssubset_K45 : Logic.K4 ⊂ Logic.K45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 2, λ x y => x < y⟩,
          λ w _ => w = 1
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨by omega⟩;
      . suffices (0 : M.World) ≺ 1 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . trivial;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.K4 Logic.K45 := ⟨K4_ssubset_K45⟩

theorem K5_ssubset_K45 : Logic.K5 ⊂ Logic.K45 := by
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
      . refine ⟨by unfold Euclidean; omega⟩;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ z, x ≺ z ∧ ¬z = 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y; tauto;
        . exact ⟨1, by omega, 2, by omega, by trivial⟩;
instance : ProperSublogic Logic.K5 Logic.K45 := ⟨K5_ssubset_K45⟩

theorem K_ssubset_KD : Logic.K ⊂ Logic.KD := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      rw [K.Kripke.all];
      tauto;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . trivial;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K Logic.KD := ⟨K_ssubset_KD⟩

theorem K_ssubset_K4 : Logic.K ⊂ Logic.K4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      rw [K.Kripke.all];
      tauto;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≠ y⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor
      . trivial;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro x;
          match x with
          | 0 => tauto;
          | 1 => tauto;
        . exact ⟨1, by omega, 0, by omega, by trivial⟩;
instance : ProperSublogic Logic.K Logic.K4 := ⟨K_ssubset_K4⟩

theorem K_ssubset_K5 : Logic.K ⊂ Logic.K5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K5 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      rw [K.Kripke.all];
      tauto;
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x _ => x = 0⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), ¬x = 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;
instance : ProperSublogic Logic.K Logic.K5 := ⟨K_ssubset_K5⟩

theorem K_ssubset_KB : Logic.K ⊂ Logic.KB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB ⊢! φ ∧ ¬FrameClass.all ⊧ φ by
      rw [K.Kripke.all];
      tauto;
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . trivial;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;
instance : ProperSublogic Logic.K Logic.KB := ⟨K_ssubset_KB⟩

theorem S4_ssubset_S5 : Logic.S4 ⊂ Logic.S5 := by
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
instance : ProperSublogic Logic.S4 Logic.S5 := ⟨S4_ssubset_S5⟩

lemma K_ssubset_KT : Logic.K ⊂ Logic.KT := by
  trans;
  . exact K_ssubset_KD;
  . exact KD_ssubset_KT;

lemma KD_ssubset_S4 : Logic.KD ⊂ Logic.S4 := by
  trans Logic.KT;
  . exact KD_ssubset_KT;
  . exact KT_ssubset_S4;

end LO.Modal.Logic

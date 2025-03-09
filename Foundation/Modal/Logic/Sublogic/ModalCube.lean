import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Kripke.KH_Incompleteness

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem KTB_ssubset_S5 : Logic.KTB ⊂ Logic.S5 := by
  constructor;
  . rw [KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic, S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_eucl⟩;
    apply hφ;
    refine ⟨F_refl, symm_of_refl_eucl F_refl F_eucl⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬Kripke.FrameClass.refl_symm ⊧ φ by simpa [KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = 1 ∧ y ≠ 2) ∨ (x = 2 ∧ y ≠ 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . unfold Reflexive;
          omega;
        . unfold Symmetric;
          omega;
      . suffices (0 : M.World) ≺ 1 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          constructor <;> omega;
instance : ProperSublogic Logic.KTB Logic.S5 := ⟨KTB_ssubset_S5⟩

theorem KD45_ssubset_S5 : Logic.KD45 ⊂ Logic.S5 := by
  constructor;
  . rw [KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic, S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_eucl⟩;
    apply hφ;
    refine ⟨?_, ?_, F_eucl⟩;
    . exact serial_of_refl F_refl;
    . exact trans_of_refl_eucl F_refl F_eucl;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬SerialTransitiveEuclideanFrameClass ⊧ φ by simpa [KD45.eq_SerialTransitiveEuclideanKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1)⟩, λ x _ => x = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_, ?_⟩;
        . intro x;
          match x with
          | 0 => use 1; tauto;
          | 1 => use 1; tauto;
        . unfold Transitive; omega;
        . unfold Euclidean; omega;
      . simp [Semantics.Realize, Satisfies, M];
        tauto;
instance : ProperSublogic Logic.KD45 Logic.S5 := ⟨KD45_ssubset_S5⟩

theorem KB4_ssubset_S5 : Logic.KB4 ⊂ Logic.S5 := by
  constructor;
  . rw [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic, S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_eucl⟩;
    apply hφ;
    refine ⟨symm_of_refl_eucl F_refl F_eucl, trans_of_refl_eucl F_refl F_eucl⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬SymmetricTransitiveFrameClass ⊧ φ by simpa [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ x _ => False⟩, 0;
      constructor;
      . simp [Transitive, Symmetric];
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KB4 Logic.S5 := ⟨KB4_ssubset_S5⟩

theorem KT_ssubset_KTB : Logic.KT ⊂ Logic.KTB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬Kripke.FrameClass.refl ⊧ φ by simpa [KT.eq_ReflexiveKripkeFrameClass_Logic];
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
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
  . rw [KDB.eq_SerialSymmetricKripkeFrameClass_Logic, KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_symm⟩;
    apply hφ;
    refine ⟨serial_of_refl F_refl, F_symm⟩;
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬SerialSymmetricFrameClass ⊧ φ by simpa [KDB.eq_SerialSymmetricKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Bool, λ x y => x ≠ y⟩,
          λ x _ => x = true
        ⟩;
      use M, false;
      constructor;
      . refine ⟨?_, ?_⟩;
        . intro x;
          use !x;
          simp [M];
        . simp_all [Symmetric, M]
      . simp [Semantics.Realize, Satisfies, M];
        tauto;
instance : ProperSublogic Logic.KDB Logic.KTB := ⟨KDB_ssubset_KTB⟩

theorem KT_ssubset_S4 : Logic.KT ⊂ Logic.S4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomT!]) |>.subset;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬Kripke.FrameClass.refl ⊧ φ by simpa [KT.eq_ReflexiveKripkeFrameClass_Logic];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => (x = 0 ∧ y ≠ 2) ∨ (x = 1 ∧ y ≠ 0) ∨ (x = 2 ∧ y = 2)⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . intro x; omega;
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
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬SerialTransitiveFrameClass ⊧ φ by simpa [KD4.eq_SerialTransitiveKripkeFrameClass_Logic];
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . simp [Serial]
        . simp [Transitive];
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KD4 Logic.S4 := ⟨KD4_ssubset_S4⟩

theorem KD4_ssubset_KD45 : Logic.KD4 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬SerialTransitiveFrameClass ⊧ φ by simpa [KD4.eq_SerialTransitiveKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => x = y ∨ x < y⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . tauto;
        . unfold Transitive;
          omega;
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
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬SerialEuclideanFrameClass ⊧ φ by simpa [KD5.eq_SerialEuclideanKripkeFrameClass_Logic];
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . intro x;
          match x with
          | 0 => use 1; tauto;
          | 1 => use 1; omega;
          | 2 => use 2; omega;
        . unfold Euclidean; omega;
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
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬TransitiveEuclideanFrameClass ⊧ φ by simpa [K45.eq_TransitiveEuclideanKripkeFrameClass_Logic];
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => False⟩, λ w _ => True⟩;
      use M, 0;
      constructor;
      . simp [Transitive, Euclidean];
      . simp [M, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K45 Logic.KD45 := ⟨K45_ssubset_KD45⟩

theorem K45_ssubset_KB4 : Logic.K45 ⊂ Logic.KB4 := by
  constructor;
  . rw [K45.eq_TransitiveEuclideanKripkeFrameClass_Logic, KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_symm, F_trans⟩;
    apply hφ;
    refine ⟨F_trans, eucl_of_symm_trans F_symm F_trans⟩;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬TransitiveEuclideanFrameClass ⊧ φ by simpa [K45.eq_TransitiveEuclideanKripkeFrameClass_Logic];
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . tauto;
        . unfold Euclidean; tauto;
      . simp [M, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K45 Logic.KB4 := ⟨K45_ssubset_KB4⟩

theorem KB_ssubset_KB4 : Logic.KB ⊂ Logic.KB4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB4 ⊢! φ ∧ ¬SymmetricFrameClass ⊧ φ by simpa [KB.eq_SymmetricKripkeFrameClass_Logic];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩;
      use M, false;
      constructor;
      . simp [Symmetric, M];
      . simp [M, Semantics.Realize, Satisfies];
        tauto;
instance : ProperSublogic Logic.KB Logic.KB4 := ⟨KB_ssubset_KB4⟩

theorem KD_ssubset_KT : Logic.KD ⊂ Logic.KT := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp [axiomK!, axiomD!]) |>.subset;
  . suffices ∃ φ, Hilbert.KT ⊢! φ ∧ ¬SerialFrameClass ⊧ φ by simpa [KD.eq_SerialKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . tauto;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KD Logic.KT := ⟨KD_ssubset_KT⟩

theorem KD_ssubset_KDB : Logic.KD ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬SerialFrameClass ⊧ φ by simpa [KD.eq_SerialKripkeFrameClass_Logic];
    use Axioms.B (.atom 0);
    constructor;
    . exact axiomB!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . intro x;
        match x with
        | 0 => use 1; tauto;
        | 1 => use 1;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor <;> omega;
instance : ProperSublogic Logic.KD Logic.KDB := ⟨KD_ssubset_KDB⟩

theorem KB_ssubset_KDB : Logic.KB ⊂ Logic.KDB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KDB ⊢! φ ∧ ¬SymmetricFrameClass ⊧ φ by simpa [KB.eq_SymmetricKripkeFrameClass_Logic];
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => w = 0⟩, 0;
      constructor;
      . simp [Symmetric];
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.KB Logic.KDB := ⟨KB_ssubset_KDB⟩

theorem KD_ssubset_KD4 : Logic.KD ⊂ Logic.KD4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬SerialFrameClass ⊧ φ by simpa [KD.eq_SerialKripkeFrameClass_Logic];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Bool, λ x y => x != y⟩, λ w _ => w = true⟩;
      use M, false;
      constructor;
      . simp [Serial, M];
      . simp [M, Semantics.Realize, Satisfies];
        tauto;
instance : ProperSublogic Logic.KD Logic.KD4 := ⟨KD_ssubset_KD4⟩

theorem K4_ssubset_KD4 : Logic.K4 ⊂ Logic.KD4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬Kripke.FrameClass.transitive ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 1, λ x y => False⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K4 Logic.KD4 := ⟨K4_ssubset_KD4⟩

lemma K4_ssubset_S4 : Logic.K4 ⊂ Logic.S4 := by
  trans;
  . exact K4_ssubset_KD4
  . exact KD4_ssubset_S4

theorem KD_ssubset_KD5 : Logic.KD ⊂ Logic.KD5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬SerialFrameClass ⊧ φ by simpa [KD.eq_SerialKripkeFrameClass_Logic];
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
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
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬Kripke.FrameClass.eucl ⊧ φ by simpa [K5.eq_EuclideanKripkeFrameClass_Logic];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 1, λ x y => False⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K5 Logic.KD5 := ⟨K5_ssubset_KD5⟩

theorem K4_ssubset_K45 : Logic.K4 ⊂ Logic.K45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬Kripke.FrameClass.transitive ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 2, λ x y => x < y⟩,
          λ w _ => w = 1
        ⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq, Transitive];
        omega;
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
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬Kripke.FrameClass.eucl ⊧ φ by simpa [K5.eq_EuclideanKripkeFrameClass_Logic];
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq, Euclidean]; omega;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ z, x ≺ z ∧ ¬z = 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y; tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            constructor;
            . omega;
            . trivial;
instance : ProperSublogic Logic.K5 Logic.K45 := ⟨K5_ssubset_K45⟩

theorem K_ssubset_KD : Logic.K ⊂ Logic.KD := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩;
      use M, 0;
      constructor;
      . tauto;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.K Logic.KD := ⟨K_ssubset_KD⟩

theorem K_ssubset_K4 : Logic.K ⊂ Logic.K4 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≠ y⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor
      . tauto;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro x;
          match x with
          | 0 => tauto;
          | 1 => tauto;
        . use 1;
          constructor;
          . omega;
          . use 0;
            constructor;
            . omega;
            . trivial;
instance : ProperSublogic Logic.K Logic.K4 := ⟨K_ssubset_K4⟩

theorem K_ssubset_K5 : Logic.K ⊂ Logic.K5 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K5 ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.Five (.atom 0));
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x _ => x = 0⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices ∃ (x : M.World), ¬x = 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;
instance : ProperSublogic Logic.K Logic.K5 := ⟨K_ssubset_K5⟩

theorem K_ssubset_KB : Logic.K ⊂ Logic.KB := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KB ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.B (.atom 0));
    constructor;
    . exact axiomB!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . tauto;
      . suffices ∃ (x : M.World), (0 : M.World) ≺ x ∧ ¬x ≺ 0 by simpa [Semantics.Realize, Satisfies, M];
        use 1;
        trivial;
instance : ProperSublogic Logic.K Logic.KB := ⟨K_ssubset_KB⟩

theorem S4_ssubset_S5 : Logic.S4 ⊂ Logic.S5 := by
  constructor;
  . rw [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic, S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_eucl⟩;
    apply hφ;
    refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬Kripke.FrameClass.preorder ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w _ => w = 2)⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ?_⟩;
        . tauto;
        . simp [Transitive];
          omega;
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.S4 Logic.S5 := ⟨S4_ssubset_S5⟩

lemma K_ssubset_KT : Logic.K ⊂ Logic.KT := by
  trans;
  . exact K_ssubset_KD;
  . exact KD_ssubset_KT;

end LO.Modal.Logic

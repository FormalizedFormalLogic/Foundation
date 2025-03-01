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
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬ReflexiveSymmetricFrameClass ⊧ φ by simpa [KTB.eq_ReflexiveSymmetricKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.KTB ⊢! φ ∧ ¬ReflexiveFrameClass ⊧ φ by simpa [KT.eq_ReflexiveKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬ReflexiveFrameClass ⊧ φ by simpa [KT.eq_ReflexiveKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.KD4 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
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

instance : ProperSublogic Logic.K4 Logic.K4Dot2 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Dot2 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.WeakDot2 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakDot2!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x = 0⟩,
        λ w a => if a = 0 then True else w = 0
      ⟩;
      use M, 0;
      constructor;
      . simp [Transitive, M];
      . suffices ∃ (x : M.World), (∀ y, ¬x ≺ y) ∧ x ≠ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor;
        . omega;
        . trivial;
⟩

instance : ProperSublogic Logic.K4Dot2 Logic.S4Dot2 := ⟨by
  constructor;
  . rw [K4Dot2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic, S4Dot2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨F_trans, ?_⟩;
    . rintro x y z ⟨Rxy, Ryz, _⟩;
      exact F_conn ⟨Rxy, Ryz⟩;
  . suffices ∃ φ, Hilbert.S4Dot2 ⊢! φ ∧ ¬TransitiveWeakConfluentFrameClass ⊧ φ by simpa [K4Dot2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic];
    use (Axioms.Dot2 (.atom 0));
    constructor;
    . exact axiomDot2!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . unfold M;
        constructor;
        . simp [Transitive]; omega;
        . simp [WeakConfluent]; omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . omega;
        . use 1; omega;
⟩

instance : ProperSublogic Logic.K4 Logic.K4Dot3 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Dot3 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.WeakDot3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakDot3!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∧ y ≠ 0⟩,
        λ w a => if a = 0 then w = 1 else w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp [M, Transitive];
        omega;
      . suffices
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 1 ∧ (∀ y, x ≺ y → y = 1) ∧ ¬x = 2 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 2 ∧ (∀ z : M.World, x ≺ z → z = 2) ∧ x ≠ 1
          by simpa [M, Semantics.Realize, Satisfies];
        refine ⟨1, ?_, rfl, ?_, ?_, 2, ?_, rfl, ?_, ?_⟩;
        . trivial;
        . omega;
        . trivial;
        . omega;
        . trivial;
        . trivial;
⟩

instance : ProperSublogic Logic.K4Dot3 Logic.S4Dot3 := ⟨by
  constructor;
  . rw [K4Dot3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic, S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨F_trans, ?_⟩;
    . rintro x y z ⟨Rxy, Ryz, _⟩;
      exact F_conn ⟨Rxy, Ryz⟩;
  . suffices ∃ φ, Hilbert.S4Dot3 ⊢! φ ∧ ¬TransitiveWeakConnectedFrameClass ⊧ φ by simpa [K4Dot3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic];
    use (Axioms.Dot3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomDot3!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . unfold M;
        constructor;
        . simp [Transitive]; omega;
        . simp [WeakConnected];
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;
⟩

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
  . suffices ∃ φ, Hilbert.KD5 ⊢! φ ∧ ¬EuclideanFrameClass ⊧ φ by simpa [K5.eq_EuclideanKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬EuclideanFrameClass ⊧ φ by simpa [K5.eq_EuclideanKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.KD ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.K4 ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.K5 ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
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
  . suffices ∃ φ, Hilbert.KB ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
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


lemma K_ssubset_KT : Logic.K ⊂ Logic.KT := by
  trans;
  . exact K_ssubset_KD;
  . exact KD_ssubset_KT;


theorem K4_ssubset_GL : Logic.K4 ⊂ Logic.GL := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.K4 ⊢! φ by simpa;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact Hilbert.K4.unprovable_AxiomL;
instance : ProperSublogic Logic.K4 Logic.GL := ⟨K4_ssubset_GL⟩


theorem S4_ssubset_S4Dot2 : Logic.S4 ⊂ Logic.S4Dot2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Dot2 ⊢! φ ∧ ¬ReflexiveTransitiveFrameClass ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Dot2 (.atom 0)
    constructor;
    . exact axiomDot2!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = y) ⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . constructor;
        . simp [M, Reflexive];
        . unfold Transitive;
          omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, x ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨by omega, ?_, ?_⟩;
        . intro y;
          match y with
          | 0 => omega;
          | 1 => tauto;
          | 2 => omega;
        . use 2;
          constructor;
          . omega;
          . omega;
instance : ProperSublogic Logic.S4 Logic.S4Dot2 := ⟨S4_ssubset_S4Dot2⟩


theorem S4Dot2_ssubset_S4Dot3 : Logic.S4Dot2 ⊂ Logic.S4Dot3 := by
  constructor;
  . rw [S4Dot2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic, S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨?_, ?_, ?_⟩;
    . exact F_refl;
    . exact F_trans;
    . exact confluent_of_refl_connected F_refl F_conn;
  . suffices ∃ φ, Hilbert.S4Dot3 ⊢! φ ∧ ¬ReflexiveTransitiveConfluentFrameClass ⊧ φ by
      simpa [S4Dot2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic];
    use Axioms.Dot3 (.atom 0) (.atom 1);
    constructor;
    . exact axiomDot3!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 4, λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)⟩, λ w a => (a = 0 ∧ (w = 1 ∨ w = 3)) ∨ (a = 1 ∧ (w = 2 ∨ w = 3))⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine ⟨?_, ?_, ?_⟩;
        . simp [M, Reflexive]; omega;
        . simp [M, Transitive]; omega;
        . rintro x y z ⟨Rxy, Ryz⟩;
          use 3;
          constructor <;> omega;
      . apply Kripke.Satisfies.or_def.not.mpr;
        push_neg;
        constructor;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 1;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;
instance : ProperSublogic Logic.S4Dot2 Logic.S4Dot3 := ⟨S4Dot2_ssubset_S4Dot3⟩


theorem S4Dot3_ssubset_S5 : Logic.S4Dot3 ⊂ Logic.S5 := by
  constructor;
  . rw [S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic, S5.eq_UniversalKripkeFrameClass_Logic];
    rintro φ hφ F F_univ;
    apply hφ;
    refine ⟨?_, ?_, ?_⟩;
    . unfold Reflexive; intros; apply F_univ;
    . unfold Transitive; intros; apply F_univ;
    . unfold Connected; intros; constructor; apply F_univ;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬ReflexiveTransitiveConnectedFrameClass ⊧ φ by
      simpa [S4Dot3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w a => (w = 0)⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine ⟨?_, ?_, ?_⟩;
        . simp [M, Reflexive];
        . simp [M, Transitive]; omega;
        . rintro x y z ⟨Rxy, Ryz⟩; omega;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.S4Dot3 Logic.S5 := ⟨S4Dot3_ssubset_S5⟩


lemma S4_ssubset_S5 : Logic.S4 ⊂ Logic.S5 := by
  trans Logic.S4Dot2;
  . exact S4_ssubset_S4Dot2;
  . trans Logic.S4Dot3;
    . exact S4Dot2_ssubset_S4Dot3;
    . exact S4Dot3_ssubset_S5;


theorem S4_ssubset_Grz : Logic.S4 ⊂ Logic.Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Grz ⊢! φ ∧ ¬ReflexiveTransitiveFrameClass ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      simp [Reflexive, Transitive, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S4 Logic.Grz := ⟨S4_ssubset_Grz⟩

lemma S5Grz_eq_Triv : Logic.S5Grz = Logic.Triv := by
  ext φ;
  exact Hilbert.iff_provable_S5Grz_provable_Triv;

lemma S5_ssubset_S5Grz : Logic.S5 ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬UniversalFrameClass ⊧ φ by simpa [S5.eq_UniversalKripkeFrameClass_Logic];
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      simp [Universal, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S5 Logic.S5Grz := ⟨S5_ssubset_S5Grz⟩

theorem S5_ssubset_Triv : Logic.S5 ⊂ Logic.Triv := by
  convert S5_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.S5 Logic.Triv := ⟨S5_ssubset_Triv⟩

-- TODO: more refactor for operating finite frame
lemma Grz_ssubset_S5Grz : Logic.Grz ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬ReflexiveTransitiveAntiSymmetricFiniteFrameClass ⊧ φ by simpa [Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0)
    constructor;
    . exact axiomFive!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_frame;
      let F : FiniteFrame := ⟨Fin 2, λ x y => x ≤ y⟩;
      use F.toFrame;
      constructor;
      . use F;
        refine ⟨⟨?_, ?_, ?_⟩, rfl⟩;
        . simp [F, Reflexive];
        . simp [F, Transitive]; omega;
        . simp [F, AntiSymmetric]; omega;
      . apply ValidOnFrame.not_of_exists_valuation_world;
        use (λ w _ => w = 0), 0;
        suffices (0 : F.World) ≺ 0 ∧ ∃ x, (0 : F.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

theorem Grz_ssubset_Triv : Logic.Grz ⊂ Logic.Triv := by
  convert Grz_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.Grz Logic.Triv := ⟨Grz_ssubset_Triv⟩

theorem GL_ssubset_Ver : Logic.GL ⊂ Logic.Ver := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬Hilbert.GL ⊢! φ by simpa;
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . by_contra hC;
      have := unnec! hC;
      have := Hilbert.GL.Kripke.consistent.not_bot;
      contradiction
instance : ProperSublogic Logic.GL Logic.Ver := ⟨GL_ssubset_Ver⟩

theorem KH_ssubset_GL : Logic.KH ⊂ Logic.GL := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.KH ⊢! φ by simpa;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . exact KH_unprov_axiomFour;
instance : ProperSublogic Logic.KH Logic.GL := ⟨KH_ssubset_GL⟩

theorem K_ssubset_KH : Logic.K ⊂ Logic.KH := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KH ⊢! φ ∧ ¬AllFrameClass ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.H (.atom 0));
    constructor;
    . exact axiomH!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩, 0;
      simp [Satisfies, Semantics.Realize];
      constructor <;> tauto;
instance : ProperSublogic Logic.K Logic.KH := ⟨K_ssubset_KH⟩


instance : ProperSublogic Logic.KTc Logic.Triv := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬CoreflexiveFrameClass ⊧ φ by
      simpa [KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . simp [Coreflexive];
      . simp [Satisfies, Semantics.Realize];
⟩

instance : ProperSublogic Logic.KTc Logic.Ver := ⟨by
  constructor;
  . rw [KTc.eq_CoreflexiveKripkeFrameClass_Logic, Ver.eq_IsolatedFrameClass_Logic];
    rintro φ hφ F F_iso;
    apply hφ;
    simp_all [Coreflexive, Isolated];
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬CoreflexiveFrameClass ⊧ φ by
      simpa [KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩;
      use M, 0;
      constructor;
      . simp [M, Coreflexive]; aesop;
      . suffices ∃ x, (0 : M.World) ≺ x by simpa [Satisfies, Semantics.Realize];
        use 0;
⟩

instance : ProperSublogic Logic.KB4 Logic.KTc := ⟨by
  constructor;
  . rw [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic, KTc.eq_CoreflexiveKripkeFrameClass_Logic];
    rintro φ hφ F F_corefl;
    apply hφ;
    refine ⟨?_, ?_⟩;
    . intro x y Rxy;
      rw [F_corefl Rxy] at *;
      assumption;
    . intro x y z Rxy Ryz;
      rw [F_corefl Rxy, F_corefl Ryz] at *;
      assumption;
  . suffices ∃ φ, Hilbert.KTc ⊢! φ ∧ ¬SymmetricTransitiveFrameClass ⊧ φ by
      simpa [KB4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use (Axioms.Tc (.atom 0));
    constructor;
    . exact axiomTc!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . simp [Symmetric, Transitive, M];
      . suffices ∃ x, (x : M.World) ≠ 0 by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        use 1;
        aesop;
⟩

end LO.Modal.Logic

import Foundation.Modal.Hilbert.Maximal.Unprovability
import Foundation.Modal.Kripke.Hilbert.GL.Completeness
import Foundation.Modal.Kripke.Hilbert.Grz.Completeness
import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.Hilbert.KD
import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.Hilbert.S5
import Foundation.Modal.Kripke.Hilbert.Triv
import Foundation.Modal.Kripke.Hilbert.Ver
import Foundation.Modal.Logic.Basic
import Foundation.Modal.System.KT

namespace LO.Modal

namespace Logic

protected abbrev K4 : Logic := Hilbert.K4.logic

instance : (Logic.K4).Normal := Hilbert.normal

lemma K4.eq_TransitiveKripkeFrameClass_Logic : Logic.K4 = Kripke.TransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev KD : Logic := Hilbert.KD.logic

instance : (Logic.KD).Normal := Hilbert.normal

lemma KD.eq_SerialKripkeFrameClass_Logic : Logic.KD = Kripke.SerialFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic



protected abbrev KT : Logic := Hilbert.KT.logic

instance : (Logic.KT).Normal := Hilbert.normal

lemma KT.eq_TransitiveKripkeFrameClass_Logic : Logic.KT = Kripke.ReflexiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S4 : Logic := Hilbert.S4.logic

instance : (Logic.S4).Normal := Hilbert.normal

lemma S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic : Logic.S4 = Kripke.ReflexiveTransitiveFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev S5 : Logic := Hilbert.S5.logic

instance : (Logic.S5).Normal := Hilbert.normal

lemma S5.eq_ReflexiveEuclideanKripkeFrameClass_Logic : Logic.S5 = Kripke.ReflexiveEuclideanFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev GL : Logic := Hilbert.GL.logic

instance : (Logic.GL).Normal := Hilbert.normal

lemma GL.eq_TransitiveIrreflexiveFiniteKripkeFrameClass_Logic : Logic.GL = Kripke.TransitiveIrreflexiveFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic


protected abbrev Grz : Logic := Hilbert.Grz.logic

instance : (Logic.Grz).Normal := Hilbert.normal

lemma Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic : Logic.Grz = Kripke.ReflexiveTransitiveAntiSymmetricFiniteFrameClass.logic
  := eq_Hilbert_Logic_KripkeFiniteFrameClass_Logic


protected abbrev Triv : Logic := Hilbert.Triv.logic

instance : (Logic.Triv).Normal := Hilbert.normal

lemma Triv.eq_EqualityKripkeFrameClass_Logic : Logic.Triv = Kripke.EqualityFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


protected abbrev Ver : Logic := Hilbert.Ver.logic

instance : (Logic.Ver).Normal := Hilbert.normal

lemma Ver.eq_IsolatedFrameClass_Logic : Logic.Ver = Kripke.IsolatedFrameClass.logic
  := eq_Hilbert_Logic_KripkeFrameClass_Logic


end Logic



namespace Logic

open Formula
open System
open Kripke

theorem K_ssubset_KD : (Logic.K) ⊂ (Logic.KD) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!];
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

theorem KD_ssubset_KT : (Logic.KD) ⊂ (Logic.KT) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!, axiomD!];
  . suffices ∃ φ, Hilbert.KT ⊢! φ ∧ ¬SerialFrameClass ⊧ φ by simpa [KD.eq_SerialKripkeFrameClass_Logic];
    use (Axioms.T (.atom 0));
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => y = 1⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . tauto;
      . simp [Semantics.Realize, Satisfies];

theorem K_ssubset_KT : (Logic.K) ⊂ (Logic.KT) := by
  trans;
  . exact K_ssubset_KD;
  . exact KD_ssubset_KT;

theorem K_ssubset_K4 : (Logic.K) ⊂ (Logic.K4) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!];
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

theorem KT_ssubset_S4 : (Logic.KT) ⊂ (Logic.S4) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!, axiomT!];
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬ReflexiveFrameClass ⊧ φ by simpa [KT.eq_TransitiveKripkeFrameClass_Logic];
    use Axioms.Four (.atom 0);
    constructor;
    . exact axiomFour!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
          ⟨
            Fin 3,
            λ x y =>
              match x, y with
              | 0, 0 => True
              | 0, 1 => True
              | 1, 1 => True
              | 1, 2 => True
              | 2, 2 => True
              | _, _ => False
          ⟩,
          λ w _ => w = 0 ∨ w = 1
        ⟩;
      use M, 0;
      constructor;
      . intro x;
        match x with
        | 0 => tauto;
        | 1 => tauto;
        | 2 => tauto;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y hy;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            refine ⟨by tauto, by trivial, by trivial⟩;

theorem K4_ssubset_S4 : (Logic.K4) ⊂ (Logic.S4) := by
  constructor;
  . apply Hilbert.K4_weakerThan_S4;
  . suffices ∃ φ, Hilbert.S4 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use Axioms.T (.atom 0);
    constructor;
    . exact axiomT!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 3, λ _ y => y = 1⟩, (λ w _ => w = 1)⟩, 0;
      constructor;
      . simp [Transitive];
      . simp [Semantics.Realize, Satisfies];

theorem K4_ssubset_GL : (Logic.K4) ⊂ (Logic.GL) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!, axiomFour!];
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.K4 ⊢! φ by simpa;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact Hilbert.K4.unprovable_AxiomL;

theorem S4_ssubset_Triv : (Logic.S4) ⊂ (Logic.Triv) := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms $ by simp [axiomK!, axiomT!, axiomTc!];
  . suffices ∃ φ, Hilbert.Triv ⊢! φ ∧ ¬ReflexiveTransitiveFrameClass ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Tc (.atom 0)
    constructor;
    . exact axiomTc!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      unfold Axioms.Tc;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . constructor;
        . simp [M, Reflexive];
        . unfold Transitive;
          omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ ¬x = 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor;
        . omega;
        . trivial;

end Logic

end LO.Modal

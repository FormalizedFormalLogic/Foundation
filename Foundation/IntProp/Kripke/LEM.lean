import Foundation.IntProp.Kripke.Semantics

namespace LO.IntProp

open System
open Formula Formula.Kripke

namespace Kripke

/--
  ```
    3
   / \
  1   2
   \ /
    0
  ```
-/
abbrev diaFrame : Kripke.Frame where
  World := Fin 4
  Rel := λ x y =>
    match x, y with
    | 0, _ => True
    | 1, 3 => True
    | 2, 3 => True
    | x, y => x ≤ y
  rel_po := {
    refl := by sorry
    antisymm := λ x y =>
      match x, y with
      | 1, 2 => by simp;
      | x, y => by
        intro Rxy Ryx;
        apply LE.le.antisymm;
        . aesop;
        . aesop;
    trans := λ x y z => sorry
  }
lemma dia.confluent : Confluent diaFrame := by
  simp [Confluent];
  intro x y z Rxy Rxz;
  sorry;

end Kripke


namespace Hilbert

open Kripke

variable {a b : ℕ}

theorem Int.no_WeakLEM : ∃ a, (Hilbert.Int ℕ) ⊬ Axioms.WeakLEM (atom a) := by
  by_contra hC; simp at hC;
  -- have : Kripke.AllFrameClass ⊧ Axioms.WeakLEM (atom a) := Sound.sound hC; simp at this;
  let F : Kripke.Frame := {
    World := Fin 3
    Rel := λ x y =>
      match x, y with
      | 0, _ => True
      | x, y => x = y
    rel_po := {
      refl := by aesop;
      antisymm := by aesop;
      trans := by aesop;
    }
  }
  -- have : F ⊧ Axioms.WeakLEM (atom a) := this F;
  have : Confluent F := by
    apply @Kripke.ConfluentFrameClass.defined_by_WLEM F |>.mpr;
    simp;
    intro φ;
    induction φ using Formula.rec' with
    | hatom a =>
      apply (Hilbert.Int.Kripke.sound.sound $ hC a) F;
      tauto;
    | hfalsum => simp [ValidOnFrame, ValidOnModel, Axioms.WeakLEM, Semantics.Realize, Satisfies];
    | hverum => simp [ValidOnFrame, ValidOnModel, Axioms.WeakLEM, Semantics.Realize, Satisfies]; sorry;
    | hneg φ ih =>
      intro V x;
      apply Formula.Kripke.Satisfies.or_def.mpr;
      sorry;
    | _ => sorry;
  have : ¬Confluent F := by
    simp only [Confluent]; push_neg;
    use 0, 1, 2;
    simp;
  contradiction;

theorem Int_strictly_weaker_than_LC : (Hilbert.Int ℕ) <ₛ (Hilbert.KC ℕ) := by
  constructor;
  . exact Hilbert.Int_weaker_than_KC;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use ∼(atom default) ⋎ ∼∼(atom default);
    constructor;
    . exact wlem!;
    . exact Int.no_WeakLEM;

theorem KC.no_Dummett : (Hilbert.KC ℕ) ⊬ Axioms.Dummett (atom a) (atom b) := by
  by_contra hC;
  have : Kripke.ConfluentFrameClass ⊧ Axioms.Dummett (atom a) (atom b) := Sound.sound hC; simp at this;
  have : Kripke.diaFrame ⊧ Axioms.Dummett (atom a) (atom b) := this Kripke.diaFrame $ by
    sorry;
    /-
    simp [Confluent];
    intro x y z Rxy Ryz;
    match x, y, z with
    | 0, 1, 2 => use 3;
    | 0, 2, 1 => use 3;
    | 1, 3, 2 => use 0;
    | _, _, _ => sorry;
    -/
  have : Connected Kripke.diaFrame := by sorry;
  have : ¬Connected Kripke.diaFrame := by
    simp only [Connected]; push_neg;
    use 0, 1, 2;
    sorry; -- simp;
  contradiction;

theorem KC_strictly_weaker_than_LC : (Hilbert.KC ℕ) <ₛ (Hilbert.LC ℕ) := by
  constructor;
  . sorry;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use Axioms.Dummett (atom 0) (atom 1);
    constructor;
    . exact dummett!;
    . exact KC.no_Dummett;

theorem LC.no_LEM : (Hilbert.LC ℕ) ⊬ Axioms.LEM (atom a) := by
  by_contra hC;
  have : Kripke.ConnectedFrameClass ⊧ Axioms.LEM (atom a) := Sound.sound hC; simp at this;
  let F : Kripke.Frame := {
    World := Fin 2
    Rel := λ x y => x ≤ y
  };
  have : F ⊧ Axioms.LEM (atom a) := this _ $ by simp [Connected]; omega;
  have : Euclidean F := by sorry;
  have : ¬Euclidean F := by
    simp only [Euclidean]; push_neg;
    use 0, 0, 1;
    simp;
  contradiction;

theorem LC_strictly_weaker_than_Cl : (Hilbert.LC ℕ) <ₛ (Hilbert.Cl ℕ) := by
  constructor;
  . exact Hilbert.LC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use Axioms.LEM (atom 0);
    constructor;
    . exact lem!;
    . exact LC.no_LEM;

theorem Int_strictly_weaker_than_Cl : (Hilbert.Int ℕ) <ₛ (Hilbert.Cl ℕ) :=
  strictlyWeakerThan.trans Int_strictly_weaker_than_LC $ strictlyWeakerThan.trans KC_strictly_weaker_than_LC LC_strictly_weaker_than_Cl

end Hilbert

end LO.IntProp

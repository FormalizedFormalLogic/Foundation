import Foundation.IntProp.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.IntProp

open System
open Formula Formula.Kripke

namespace Hilbert

theorem Int.no_WeakLEM : (Hilbert.Int ℕ) ⊬ Axioms.WeakLEM (atom a) := by
  by_contra hC;
  let F : Kripke.Frame := {
    World := Fin 3,
    Rel := λ x y =>
      match x, y with
      | 0, x => True
      | x, y => x = y,
    rel_po := {
      refl := by aesop;
      antisymm := by aesop;
      trans := by aesop;
    }
  };
  have : F ⊧ Axioms.WeakLEM (atom a) := Kripke.sound.sound hC F $ by tauto;
  have : Confluent F := by sorry;
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

/-
theorem KC.no_Dummet : (Hilbert.KC ℕ) ⊬ Axioms.GD (atom a) (atom b) := by
  by_contra hC;
  let F : Kripke.Frame := {
    World := Fin 4,
    Rel := λ x y =>
      match x, y with
      | 1, 2 => False
      | x, y => x ≤ y
    rel_po := {
      refl := by aesop;
      antisymm := by sorry;
      trans := by
        intro x y z;
        aesop;
        match y with
        | 0 => simp; rintro rfl; tauto;
        | 1 =>
          match x with
          | 0 => sorry;
          | 1 => aesop;
          | _ => sorry;
        | 2 => sorry;
        | 3 => simp; rintro _ rfl; tauto;
        -- match (x, y, z) with
        -- | 0, 1, 2 => simp;
        -- | _ => sorry;
    }
  };
  have : F ⊧ Axioms.GD (atom a) (atom b) := Kripke.sound.sound hC F $ by
    simp [Confluent];
    intro x y z Rxy Ryz;
    match x, y, z with
    | 0, 1, 2 => use 3;
    | 0, 2, 1 => use 3;
    | 1, 3, 2 => use 0;
    | _, _, _ => sorry;
-/

/-
theorem KC.noLEM : (Hilbert.KC α) ⊬ (atom a) ⋎ ∼(atom a) := by
  by_contra hC;
  apply Kripke.twopoints.noLEM;
  apply Kripke.sound.sound hC;
  exact Kripke.twopoints.is_confluent;

theorem KC_strictly_weaker_than_Cl [Inhabited α] : (Hilbert.KC α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.KC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (atom default) ⋎ ∼(atom default);
    constructor;
    . exact lem!;
    . exact KC.noLEM;
-/
lemma KC.no_dummett : (Hilbert.KC ℕ) ⊬ Axioms.Dummett (atom a) (atom b) := by sorry;

theorem KC_strictly_weaker_than_LC : (Hilbert.KC ℕ) <ₛ (Hilbert.LC ℕ) := by
  constructor;
  . sorry;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use Axioms.Dummett (atom 0) (atom 1);
    constructor;
    . exact dummett!;
    . exact KC.no_dummett;

theorem LC.no_LEM : (Hilbert.LC ℕ) ⊬ Axioms.LEM (atom a) := by
  by_contra hC;
  let F : Kripke.Frame := {
    World := Fin 2,
    Rel := λ x y => x ≤ y
  };
  have : F ⊧ Axioms.LEM (atom a) := Kripke.sound.sound hC F $ by
    simp [Connected];
    omega;
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

import Foundation.IntProp.Kripke.Semantics

-- TODO: prove `Formula.Kripke.ValidOnFrame.subst`

namespace LO.IntProp

open System
open Formula Formula.Kripke

-- TODO: 成り立つのか？
lemma Formula.Kripke.ValidOnFrame.subst {F : Kripke.Frame} {φ : Formula ℕ} (h : F ⊧ φ) (s : ℕ → Formula ℕ) : F ⊧ φ.subst s := by sorry;
  /-
  induction φ using Formula.rec' with
  | hatom =>
    intro V x;
    refine h (V := ⟨λ x a => Satisfies ⟨F, V⟩ x (s a), ?_⟩) x;
    intro x y Rxy a;
    exact formula_hereditary Rxy;
  | hverum => simp;
  | hfalsum => simp at h;
  | hand _ _ hφ hψ =>
    intro V x;
    apply Satisfies.and_def.mp;
    constructor;
    . apply hφ;
      intro V x;
      exact h x |>.1;
    . apply hψ;
      intro V x;
      exact h x |>.2;
  | himp φ ψ hφ hψ =>
    apply Satisfies.imp_def.mp;
    intro y Rxy hy;
    apply hψ;
    intro V' z;
    have := @h V x;
    have := @Satisfies.imp_def ⟨F, V⟩ x φ ψ |>.mp this Rxy;
    apply h;
    . sorry;
    . sorry;
    sorry;
  | hor φ ψ hφ hψ =>
    intro V x;
    rcases Satisfies.or_def.mp $ h x with (hl | hr);
    . left;
      apply hφ;
      intro V' y;
      sorry;
    . sorry;
  | hneg φ hφ =>
    intro V x;
    apply Satisfies.neg_def.mpr;
    intro y Rxy hyφ;
    have := @h V y;
    apply hφ;
  -/

namespace Hilbert

open Kripke

variable {a b : ℕ}

theorem Int.no_WeakLEM : ∃ a, (Hilbert.Int ℕ) ⊬ Axioms.WeakLEM (atom a) := by
  by_contra hC; simp at hC;
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
  have : Confluent F := by
    apply @Kripke.ConfluentFrameClass.defined_by_WLEM F |>.mpr;
    simp [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff];
    intro φ;
    suffices ValidOnFrame F (Axioms.WeakLEM (atom 0))
      from @Formula.Kripke.ValidOnFrame.subst F (Axioms.WeakLEM (atom 0)) this (λ a => match a with | 0 => φ | _ => atom a);
    apply (Hilbert.Int.Kripke.sound.sound $ hC 0) F;
    tauto;
  have : ¬Confluent F := by
    simp only [Confluent]; push_neg;
    use 0, 1, 2;
    simp;
  contradiction;

theorem Int_strictly_weaker_than_LC : (Hilbert.Int ℕ) <ₛ (Hilbert.KC ℕ) := by
  constructor;
  . exact Hilbert.Int_weaker_than_KC;
  . obtain ⟨a, h⟩ := Int.no_WeakLEM;
    apply weakerThan_iff.not.mpr;
    push_neg;
    use ∼(atom a) ⋎ ∼∼(atom a);
    constructor;
    . exact wlem!;
    . exact h;

theorem KC.no_Dummett : ∃ a b, (Hilbert.KC ℕ) ⊬ Axioms.Dummett (atom a) (atom b) := by
  by_contra hC; simp at hC;
  let F : Kripke.Frame := {
    World := Fin 4
    Rel := λ x y =>
      match x, y with
      | 1, 2 => False
      | x, y => x ≤ y
    rel_po := {
      refl := by simp only [le_refl, implies_true];
      trans := by
        intro x y z Rxy Ryx;
        split at Rxy;
        . contradiction;
        . split at Ryx;
          . contradiction;
          . split;
            . simp_all; omega;
            . omega;
      antisymm := by
        intro x y Rxy Ryx;
        split at Rxy;
        . contradiction;
        . split at Ryx;
          . contradiction;
          . exact LE.le.antisymm Rxy Ryx;
    }
  };
  have : Connected F := by
    apply @Kripke.ConnectedFrameClass.defined_by_Dummett F |>.mpr;
    simp [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff];
    rintro _ φ ψ rfl;
    suffices ValidOnFrame F (Axioms.Dummett (atom 0) (atom 1))
      from @Formula.Kripke.ValidOnFrame.subst F (Axioms.Dummett (atom 0) (atom 1)) this (λ a => match a with | 0 => φ | 1 => ψ | _ => atom a);
    apply (Hilbert.KC.Kripke.sound.sound $ hC 0 1) F;
    simp [Confluent];
    intro x y z Rxy Ryz;
    use 3;
    split at Rxy;
    . contradiction;
    . split at Ryz;
      . contradiction;
      . constructor;
        . simp_all; omega;
        . simp_all; omega;
  have : ¬Connected F := by
    simp only [Connected]; push_neg;
    use 0, 1, 2;
    simp;
  contradiction;

theorem KC_strictly_weaker_than_LC : (Hilbert.KC ℕ) <ₛ (Hilbert.LC ℕ) := by
  constructor;
  . exact Hilbert.KC_weaker_than_LC;
  . obtain ⟨a, b, h⟩ := KC.no_Dummett;
    apply weakerThan_iff.not.mpr;
    push_neg;
    use Axioms.Dummett (atom a) (atom b);
    constructor;
    . exact dummett!;
    . exact h;

theorem LC.no_LEM : ∃ a, (Hilbert.LC ℕ) ⊬ Axioms.LEM (atom a) := by
  by_contra hC; simp at hC;
  let F : Kripke.Frame := {
    World := Fin 2
    Rel := λ x y => x ≤ y
  };
  have : Euclidean F := by
    apply @Kripke.EuclideanFrameClass.defined_by_LEM F |>.mpr;
    simp [Semantics.RealizeSet.setOf_iff, ValidOnFrame.models_iff];
    intro φ;
    suffices ValidOnFrame F (Axioms.LEM (atom 0))
      from @Formula.Kripke.ValidOnFrame.subst F (Axioms.LEM (atom 0)) this (λ a => match a with | 0 => φ | _ => atom a);
    apply (Hilbert.LC.Kripke.sound.sound $ hC 0) F;
    simp [Connected];
    omega;
  have : ¬Euclidean F := by
    simp only [Euclidean]; push_neg;
    use 0, 0, 1;
    simp;
  contradiction;

theorem LC_strictly_weaker_than_Cl : (Hilbert.LC ℕ) <ₛ (Hilbert.Cl ℕ) := by
  constructor;
  . exact Hilbert.LC_weaker_than_Cl;
  . obtain ⟨a, h⟩ := LC.no_LEM;
    apply weakerThan_iff.not.mpr;
    push_neg;
    use Axioms.LEM (atom a);
    constructor;
    . exact lem!;
    . exact h;

theorem Int_strictly_weaker_than_Cl : (Hilbert.Int ℕ) <ₛ (Hilbert.Cl ℕ) :=
  strictlyWeakerThan.trans Int_strictly_weaker_than_LC $ strictlyWeakerThan.trans KC_strictly_weaker_than_LC LC_strictly_weaker_than_Cl

end Hilbert

end LO.IntProp

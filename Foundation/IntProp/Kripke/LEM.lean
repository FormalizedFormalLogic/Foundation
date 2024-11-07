import Foundation.IntProp.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.IntProp

open System
open Formula Formula.Kripke


variable {α : Type u}

abbrev NoLEMFrame : Kripke.Frame where
  World := PUnit ⊕ PUnit
  Rel x y :=
    match x, y with
    | .inl _, .inl _ => True
    | .inr _, .inr _ => True
    | .inl _, .inr _ => True
    | _, _ => False

namespace NoLEMFrame

lemma is_transitive : Transitive NoLEMFrame.Rel := by simp [Transitive];

lemma is_reflexive : Reflexive NoLEMFrame.Rel := by simp [Reflexive];

lemma is_confluent : Confluent NoLEMFrame.Rel := by simp [Confluent];

lemma is_connected : Connected NoLEMFrame.Rel := by simp [Connected];

end NoLEMFrame


lemma Kripke.noLEM_on_frameclass [Inhabited α] : ∃ (φ : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.Int α)) ⊧ φ ⋎ ∼φ) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply Int_Characteraizable.characterize;
    exact ⟨NoLEMFrame.is_reflexive, NoLEMFrame.is_transitive⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];


/--
  Law of Excluded Middle is not always provable in intuitionistic logic.
-/
theorem Hilbert.Int.noLEM [Inhabited α] : ∃ (φ : Formula α), (Hilbert.Int α) ⊬ φ ⋎ ∼φ := by
  obtain ⟨φ, hp⟩ := Kripke.noLEM_on_frameclass (α := α);
  use φ;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

/--
  Intuitionistic logic is proper weaker than classical logic.
-/
theorem Hilbert.Int_strictly_weaker_than_Cl [DecidableEq α] [Inhabited α] : (Hilbert.Int α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.Int_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨φ, hp⟩ := Hilbert.Int.noLEM (α := α);
    use (φ ⋎ ∼φ);
    constructor;
    . exact lem!;
    . assumption;


section

lemma Kripke.noLEM_on_frameclass_KC [DecidableEq α] [Inhabited α]  : ∃ (φ : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.KC α)) ⊧ φ ⋎ ∼φ) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply Kripke.KC_Characteraizable.characterize;
    exact ⟨NoLEMFrame.is_reflexive, NoLEMFrame.is_transitive, NoLEMFrame.is_confluent⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];

lemma Hilbert.KC.noLEM [DecidableEq α] [Inhabited α] : ∃ (φ : Formula α), (Hilbert.KC α) ⊬ φ ⋎ ∼φ := by
  obtain ⟨φ, hp⟩ := Kripke.noLEM_on_frameclass_KC (α := α);
  use φ;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

theorem Hilbert.KC_strictly_weaker_than_Cl [DecidableEq α] [Inhabited α] : (Hilbert.KC α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.KC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨φ, hp⟩ := Hilbert.KC.noLEM (α := α);
    use (φ ⋎ ∼φ);
    constructor;
    . exact lem!;
    . assumption;

end


section

lemma Kripke.noLEM_on_frameclass_LC [Inhabited α] : ∃ (φ : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} (Hilbert.LC α)) ⊧ φ ⋎ ∼φ) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply LC_Characteraizable.characterize;
    exact ⟨NoLEMFrame.is_reflexive, NoLEMFrame.is_transitive, NoLEMFrame.is_connected⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];

lemma Hilbert.LC.noLEM [Inhabited α] : ∃ (φ : Formula α), (Hilbert.LC α) ⊬ φ ⋎ ∼φ := by
  obtain ⟨φ, hp⟩ := Kripke.noLEM_on_frameclass_LC (α := α);
  use φ;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

theorem Hilbert.LC_strictly_weaker_than_Cl [DecidableEq α] [Inhabited α] : (Hilbert.LC α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.LC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨φ, hp⟩ := Hilbert.LC.noLEM (α := α);
    use (φ ⋎ ∼φ);
    constructor;
    . exact lem!;
    . assumption;

end

end LO.IntProp

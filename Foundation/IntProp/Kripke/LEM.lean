import Foundation.IntProp.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.IntProp

open System
open Formula Formula.Kripke

namespace Kripke

abbrev twopointsFrame : Kripke.Frame where
  World := Unit ⊕ Unit
  Rel x y :=
    match x, y with
    | .inl _, .inl _ => True
    | .inr _, .inr _ => True
    | .inl _, .inr _ => True
    | _, _ => False
  trans_Rel := by simp [Transitive];
  refl_Rel := by simp [Reflexive];

namespace twopoints

lemma is_transitive : Transitive twopointsFrame := twopointsFrame.trans_Rel
lemma is_reflexive : Reflexive twopointsFrame := twopointsFrame.refl_Rel
lemma is_confluent : Confluent twopointsFrame := by simp [Confluent]
lemma is_connected : Connected twopointsFrame := by simp [Connected]

lemma noLEM {a : α} : ¬(twopointsFrame#α ⊧ (atom a) ⋎ ∼(atom a)) := by
  simp only [Semantics.Realize, ValidOnFrame];
  push_neg;
  use (λ w _ => match w with | .inr _ => True | .inl _ => False), by simp;
  simp [Semantics.Realize, ValidOnModel, Satisfies];

end twopoints

end Kripke


variable {a : α}

namespace Hilbert

theorem Int.noLEM : (Hilbert.Int α) ⊬ (atom a) ⋎ ∼(atom a) := by
  by_contra hC;
  apply Kripke.twopoints.noLEM;
  apply Kripke.sound.sound hC;
  tauto;

theorem Int_strictly_weaker_than_Cl [Inhabited α] : (Hilbert.Int α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.Int_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (atom default) ⋎ ∼(atom default);
    constructor;
    . exact lem!;
    . exact Int.noLEM;


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


theorem LC.noLEM : (Hilbert.LC α) ⊬ (atom a) ⋎ ∼(atom a) := by
  by_contra hC;
  apply Kripke.twopoints.noLEM;
  apply Kripke.sound.sound hC;
  exact Kripke.twopoints.is_connected;

theorem LC_strictly_weaker_than_Cl [DecidableEq α] [Inhabited α] : (Hilbert.LC α) <ₛ (Hilbert.Cl α) := by
  constructor;
  . exact Hilbert.LC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (atom default) ⋎ ∼(atom default);
    constructor;
    . exact lem!;
    . exact LC.noLEM;

end Hilbert

end LO.IntProp

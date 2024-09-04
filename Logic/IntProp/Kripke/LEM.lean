import Logic.IntProp.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.IntProp.Kripke

open System

open Formula Formula.Kripke

variable {α : Type u}
variable [DecidableEq α] [Inhabited α]

abbrev NoLEMFrame : Kripke.Frame where
  World := PUnit ⊕ PUnit
  Rel x y :=
    match x, y with
    | .inl _, .inl _ => True
    | .inr _, .inr _ => True
    | .inl _, .inr _ => True
    | _, _ => False

lemma NoLEMFrame.transitive : Transitive NoLEMFrame.Rel := by simp [Transitive];

lemma NoLEMFrame.reflexive : Reflexive NoLEMFrame.Rel := by simp [Reflexive];

lemma NoLEMFrame.confluent : Confluent NoLEMFrame.Rel := by simp [Confluent];

lemma NoLEMFrame.connected : Connected NoLEMFrame.Rel := by simp [Connected];

lemma noLEM_on_frameclass : ∃ (p : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} 𝐈𝐧𝐭) ⊧ p ⋎ ~p) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply Int_Characteraizable.characterize;
    exact ⟨NoLEMFrame.reflexive, NoLEMFrame.transitive⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];

/--
  Law of Excluded Middle is not always provable in intuitionistic logic.
-/
theorem noLEM : ∃ (p : Formula α), 𝐈𝐧𝐭 ⊬! p ⋎ ~p := by
  obtain ⟨p, hp⟩ := noLEM_on_frameclass (α := α);
  use p;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

/--
  Intuitionistic logic is proper weaker than classical logic.
-/
theorem Int_strictly_weaker_than_Cl : (𝐈𝐧𝐭 : Hilbert α) <ₛ 𝐂𝐥 := by
  constructor;
  . exact Int_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨p, hp⟩ := noLEM (α := α);
    use (p ⋎ ~p);
    constructor;
    . exact lem!;
    . assumption;



section

lemma noLEM_on_frameclass_KC : ∃ (p : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} 𝐊𝐂) ⊧ p ⋎ ~p) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply KC_Characteraizable.characterize;
    exact ⟨NoLEMFrame.reflexive, NoLEMFrame.transitive, NoLEMFrame.confluent⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];

lemma noLEM_KC: ∃ (p : Formula α), 𝐊𝐂 ⊬! p ⋎ ~p := by
  obtain ⟨p, hp⟩ := noLEM_on_frameclass_KC (α := α);
  use p;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

theorem KC_strictly_weaker_than_Cl : (𝐊𝐂 : Hilbert α) <ₛ 𝐂𝐥 := by
  constructor;
  . exact KC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨p, hp⟩ := noLEM_KC (α := α);
    use (p ⋎ ~p);
    constructor;
    . exact lem!;
    . assumption;

end


section

lemma noLEM_on_frameclass_LC : ∃ (p : Formula α), ¬((Kripke.FrameClassOfHilbert.{u, 0} 𝐋𝐂) ⊧ p ⋎ ~p) := by
  use (atom default);
  simp [Semantics.Realize];
  use NoLEMFrame;
  constructor;
  . apply LC_Characteraizable.characterize;
    exact ⟨NoLEMFrame.reflexive, NoLEMFrame.transitive, NoLEMFrame.connected⟩;
  . simp [ValidOnFrame];
    use (λ w _ => match w with | .inr _ => True | .inl _ => False);
    constructor;
    . simp;
    . simp [ValidOnModel, Satisfies];

lemma noLEM_LC: ∃ (p : Formula α), 𝐋𝐂 ⊬! p ⋎ ~p := by
  obtain ⟨p, hp⟩ := noLEM_on_frameclass_LC (α := α);
  use p;
  by_contra hC;
  have := @Kripke.sound _ _ _ hC;
  contradiction;

theorem LC_strictly_weaker_than_Cl : (𝐋𝐂 : Hilbert α) <ₛ 𝐂𝐥 := by
  constructor;
  . exact LC_weaker_than_Cl;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨p, hp⟩ := noLEM_LC (α := α);
    use (p ⋎ ~p);
    constructor;
    . exact lem!;
    . assumption;

end


end LO.IntProp.Kripke

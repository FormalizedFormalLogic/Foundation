import Logic.Propositional.Superintuitionistic.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.Propositional.Superintuitionistic.Kripke

open System

open Formula Formula.Kripke

variable {α : Type*}
variable [Inhabited α]

lemma noLEM_on_frameclass : ∃ (p : Formula α), ¬((Kripke.FrameClassOfSystem.{_, _, _, _, 0} 𝐈𝐧𝐭 α) ⊧ p ⋎ ~p) := by
  use (atom default);
  simp [Semantics.Realize];
  use ⟨
    PUnit ⊕ PUnit,
    λ x y => match x, y with
    | .inl _, .inl _ => True
    | .inr _, .inr _ => True
    | .inl _, .inr _ => True
    | _, _ => False,
  ⟩;
  constructor;
  . apply Int_Characteraizable.characterize;
    simp [Transitive, Reflexive];
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
  existsi p;
  by_contra hC;
  have := Kripke.sound hC;
  contradiction;

/--
  Intuitionistic logic is proper weaker than classical logic.
-/
theorem strictReducible_intuitionistic_classical : (𝐈𝐧𝐭 : DeductionParameter α) <ₛ 𝐂𝐥 := by
  constructor;
  . exact reducible_efq_dne;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    obtain ⟨p, hp⟩ := noLEM (α := α);
    use (p ⋎ ~p);
    constructor;
    . exact lem!;
    . assumption;

end LO.Propositional.Superintuitionistic.Kripke

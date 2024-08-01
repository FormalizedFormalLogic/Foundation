import Logic.Propositional.Superintuitionistic.Kripke.Semantics

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.Propositional.Superintuitionistic.Kripke

open System

abbrev LEMCounterexampleFrame : Kripke.Frame where
  World := PUnit ⊕ PUnit
  Rel x y :=
    match x, y with
    | .inl _, .inl _ => True
    | .inr _, .inr _ => True
    | .inl _, .inr _ => True
    | _, _ => False

lemma LEMCounterexampleFrame.reflexive : Reflexive (LEMCounterexampleFrame.Rel) := by simp [Reflexive];

lemma LEMCounterexampleFrame.transitive : Transitive (LEMCounterexampleFrame.Rel) := by simp [Transitive];

lemma LEMCounterexampleFrame.mem_IntFrameClass : LEMCounterexampleFrame ∈ 𝔽((𝐈𝐧𝐭 : DeductionParameter α)) := by
  apply Characteraizable_Int.characterize;
  constructor;
  . exact LEMCounterexampleFrame.transitive;
  . exact LEMCounterexampleFrame.reflexive;

abbrev LEMCounterexampleModel (α) : Kripke.Model α where
  Frame := LEMCounterexampleFrame
  Valuation w _ :=
    match w with
    | .inr _ => True
    | .inl _ => False

open Formula Formula.Kripke

lemma noLEM_atom {a : α} : ¬(LEMCounterexampleModel α ⊧ (atom a) ⋎ ~(atom a)) := by
  simp [ValidOnModel.iff_models, Satisfies.iff_models, ValidOnModel, Satisfies, LEMCounterexampleModel];

variable {α : Type*}
variable [Inhabited α]

lemma noLEM_on_frameclass : ∃ (p : Formula α), ¬((Kripke.FrameClassOfSystem.{_, _, _, _, 0} 𝐈𝐧𝐭) ⊧ p ⋎ ~p) := by
  use (atom default);
  simp only [ValidOnFrameClass.iff_models, ValidOnFrameClass, ValidOnFrame];
  push_neg;
  use LEMCounterexampleFrame;
  constructor;
  . exact LEMCounterexampleFrame.mem_IntFrameClass;
  . simp [ValidOnFrame];
    use (LEMCounterexampleModel α).Valuation;
    constructor;
    . simp [Kripke.Valuation.atomic_hereditary];
    . apply noLEM_atom;

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
    existsi (p ⋎ ~p);
    constructor;
    . exact lem!;
    . assumption;

end LO.Propositional.Superintuitionistic.Kripke

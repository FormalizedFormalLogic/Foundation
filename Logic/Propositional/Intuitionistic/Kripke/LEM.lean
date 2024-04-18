import Logic.Propositional.Intuitionistic.Kripke.Semantics

/-!
  # Counterexamples to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.Propositional.Intuitionistic.Kripke

open Formula

variable {β : Type}

def LEMCounterExampleModel : Kripke.Model (Fin 2) β where
  frame := λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0)
  val w _ := w = 1;
  refl := by simp [Reflexive];
  trans := by simp [Transitive]; trivial;
  hereditary := by simp; aesop;

lemma noLEM_atom {a : β} : ¬(⊧ⁱ (atom a) ⋎ ~(atom a)) := by
  simp [KripkeValid, KripkeModels, NegDefinition.neg];
  existsi _, LEMCounterExampleModel, 0;
  simp_all [LEMCounterExampleModel];

variable [Inhabited β]

/-- LEM is not always valid in intuitionistic logic. -/
theorem noLEM : ¬(∀ {p : Formula β}, ⊧ⁱ p ⋎ ~p) := by
  simp;
  existsi (atom default);
  apply noLEM_atom

end Kripke

end LO.Propositional.Intuitionistic

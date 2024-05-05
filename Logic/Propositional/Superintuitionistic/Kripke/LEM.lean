import Logic.Propositional.Superintuitionistic.Kripke.Semantics

/-!
  # Counterexamples to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.Propositional.Superintuitionistic.Kripke

def LEMCounterexampleModel : Model (𝐈𝐧𝐭 (Fin 2) α) where
  frame := λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0)
  valuation w _ := w = 1;
  hereditary := by simp; aesop;
  frame_prop := by
    simp [FrameClass.Intuitionistic];
    constructor;
    . simp [Transitive]; aesop;
    . simp [Reflexive];

open Formula Formula.Kripke

lemma noLEM_atom {a : α} : ¬(LEMCounterexampleModel ⊧ (atom a) ⋎ ~(atom a)) := by
  simp [ValidOnModel.iff_models, Satisfies.iff_models, ValidOnModel, Satisfies, LEMCounterexampleModel];
  existsi 0;
  simp_all;

variable [Inhabited α]

theorem noLEM : ¬(∀ p, (𝐈𝐧𝐭 (Fin 2) α) ⊧ p ⋎ ~p) := by
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass];
  existsi (atom default), LEMCounterexampleModel;
  apply noLEM_atom

end LO.Propositional.Superintuitionistic.Kripke

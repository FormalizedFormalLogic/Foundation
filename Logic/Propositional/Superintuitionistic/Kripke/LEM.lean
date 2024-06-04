import Logic.Propositional.Superintuitionistic.Kripke.Soundness

/-!
  # Counterexample to the Law of Excluded Middle in Intuitionistic Logic

  ## Theorems
  - `noLEM`: LEM is not always valid in intuitionistic logic.
-/

namespace LO.Propositional.Superintuitionistic.Kripke


def LEMCounterexampleModel {α : Type} : Model α where
  Frame := {
    World := Fin 2,
    Rel := λ w₁ w₂ => (w₁ = w₂) ∨ (w₁ = 0)
  };
  Valuation w _ := w = 1;
  hereditary := by aesop;

def LEMCounterexampleFrame : Frame' α := (LEMCounterexampleModel).Frame

open Formula Formula.Kripke

lemma noLEM_atom {a : α} : ¬(LEMCounterexampleModel ⊧ (atom a) ⋎ ~(atom a)) := by
  simp [ValidOnModel.iff_models, Satisfies.iff_models, ValidOnModel, Satisfies, LEMCounterexampleModel];
  use 0;
  aesop;

variable {α : Type}
variable [Inhabited α]

lemma noLEM_on_frameclass : ∃ (p : Formula α), ¬(𝔽(Ax(𝐈𝐧𝐭))) ⊧ p ⋎ ~p := by
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass];
  existsi (atom default), (LEMCounterexampleModel).Frame;
  constructor;
  . apply iff_definability_memAxiomSetFrameClass AxiomSet.EFQ.definability |>.mpr;
    trivial;
  . simp [ValidOnFrame];
    existsi (LEMCounterexampleModel).Valuation, LEMCounterexampleModel.hereditary;
    apply noLEM_atom;

theorem noLEM : ∃ (p : Formula α), 𝐈𝐧𝐭 ⊬! p ⋎ ~p := by
  obtain ⟨p, _⟩ : ∃ (p : Formula α), ¬(𝔽(Ax(𝐈𝐧𝐭))) ⊧ p ⋎ ~p := noLEM_on_frameclass;
  existsi p;
  by_contra hC;
  have : 𝔽(Ax(𝐈𝐧𝐭)) ⊧ p ⋎ ~p := sound! hC;
  contradiction;

end LO.Propositional.Superintuitionistic.Kripke

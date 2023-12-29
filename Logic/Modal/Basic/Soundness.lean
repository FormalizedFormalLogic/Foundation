import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO

namespace Modal

open Formula

variable {α β : Type u} {p : Formula α} (f : Frame β)

theorem Hilbert.LogicK.provable_soundness {p : Formula α} (f : Frame β) : (⊢ᴴ(𝗞)! p) → (⊧ᶠ[f] p) := by
  intro h;
  induction h.some <;> try {simp_all [satisfies_imp, satisfies];}
  case disj₃ p q r =>
    intro V w;
    by_cases (w ⊧ˢ[⟨f, V⟩] p) <;> simp_all [satisfies_imp, satisfies];
  case modus_ponens p q d₁ d₂ ih₁ ih₂ => exact frames_ModusPonens (ih₁ ⟨d₁⟩) (ih₂ ⟨d₂⟩);
  case necessitation p d ih => exact frames_Necessitation (ih ⟨d⟩);

theorem Hilbert.LogicK.unprovable_bot : (⊬ᴴ(𝗞)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  have w := f.nonempty.some;
  suffices ⊧ᶠ[f] (⊥ : Formula α) by simp_all [satisfies_bot]; exact this w;
  exact provable_soundness f hC;

end Modal

end LO

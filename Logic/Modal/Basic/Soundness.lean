import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO

namespace Modal

open Formula

variable {α β : Type u} {p : Formula α} (f : Frame β)

theorem Hilbert.LogicK.provable_soundness {p : Formula α} (f : Frame β) : (⊢ᴴ(𝗞)! p) → (⊧ᶠ[f] p) := by
  intro h;
  cases' h.some <;> simp_all [satisfies_imp, satisfies];
  case disj₃ p =>
    intro V w;
    by_cases (w ⊧ˢ[⟨f, V⟩] p) <;> simp_all;
  case modus_ponens q d₁ d₂ => exact frames_ModusPonens (provable_soundness f (Nonempty.intro d₂)) (provable_soundness f (Nonempty.intro d₁));
  case necessitation q d => exact frames_Necessitation $ provable_soundness f (Nonempty.intro d);
  termination_by provable_soundness p f d => (d.some.length)

theorem Hilbert.LogicK.unprovable_bot : (⊬ᴴ(𝗞)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  have w := f.nonempty.some;
  suffices ⊧ᶠ[f] (⊥ : Formula α) by simp_all [satisfies_bot]; exact this w;
  exact provable_soundness f hC;

end Modal

end LO

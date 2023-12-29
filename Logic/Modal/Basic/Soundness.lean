import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO.Modal

namespace Hilbert

open Formula

variable {α β : Type u} {p : Formula α} (f : Frame β)

lemma LogicK.sounds' {p : Formula α} (f : Frame β) : (⊢ᴴ(𝗞) p) → (⊧ᶠ[f] p) := by
  intro h;
  simp [ProofH] at h;
  sorry;
  -- TODO: この帰納法が回ればいいのだが上手くいってない
  -- induction h using DerivationH.rec' <;> simp;

  /--
  induction h.some using bbb <;> try {simp_all [satisfies_imp, satisfies];}
  case disj₃ p q r =>
    intro V w;
    by_cases (w ⊧ˢ[⟨f, V⟩] p) <;> simp_all [satisfies_imp, satisfies];
  case modus_ponens p q d₁ d₂ ih₁ ih₂ => exact frames_ModusPonens (ih₁ ⟨d₁⟩) (ih₂ ⟨d₂⟩);
  case necessitation p d ih => exact frames_Necessitation (ih ⟨d⟩);
  -/

lemma LogicK.sounds {p : Formula α} (f : Frame β) : (h : ⊢ᴴ(𝗞)! p) → (⊧ᶠ[f] p) := by
  intro h; exact sounds' f h.some;

theorem LogicK.unprovable_bot : (⊬ᴴ(𝗞)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  have w := f.nonempty.some;
  suffices ⊧ᶠ[f] (⊥ : Formula α) by simp_all [satisfies_bot]; exact this w;
  exact sounds f hC;

end Hilbert

end LO.Modal

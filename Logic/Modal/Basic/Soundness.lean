import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO.Modal

namespace Hilbert

open Formula

variable {α β : Type u}

theorem LogicK.sounds (Γ : Set (Formula α)) (p : Formula α) (f : Frame β) (d : Γ ⊢ᴴ(𝐊) p) : (Γ ⊨ᶠ[f] p) := by
  induction d <;> try {simp_all [satisfies_imp, satisfies];}
  case wk _ _ _ hΓΔ _ ih =>
    apply FrameConsequence.preserveWeakening hΓΔ ih;
  case maxm Γ p ih =>
    let ⟨_, ⟨_, hq⟩⟩ := ih; rw [←hq];
    apply FrameConsequence.preserveAxiomK;
  case disj₃ p q r =>
    intro V w;
    by_cases (w ⊧ˢ[⟨f, V⟩] p) <;> simp_all [satisfies_imp, satisfies];
  case necessitation _ p _ ih =>
    exact FrameConsequence.preserveNecessitation ih;

lemma LogicK.sounds' {p : Formula α} (f : Frame β) (h : ⊢ᴴ(𝐊)! p) : (⊧ᶠ[f] p) := by
  simpa using sounds ∅ p f h.some;

theorem LogicK.unprovable_bot {f : Frame β} : (⊬ᴴ(𝐊)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ⊧ᶠ[f] (⊥ : Formula α) by exact frames_bot h;
  exact sounds' f hC;

end Hilbert

end LO.Modal

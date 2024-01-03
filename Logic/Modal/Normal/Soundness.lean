import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Formula FrameConsequence

variable {α β : Type u}

/-
  TODO: より一般にこの形で証明できる事実ではないだろうか？
  [LogicK.Hilbert Bew] (Γ : Set (Formula α)) (hΓ : Γ = ∅) (p : Formula α) (f : Frame β) (d : Bew Γ p) : (Γ ⊨ᴹᶠ[f] p)
-/
lemma LogicK.Hilbert.sounds' (Γ : Set (Formula α)) (hΓ : Γ = ∅) (p : Formula α) (f : Frame β) (d : Γ ⊢ᴹ(𝐊) p) : (Γ ⊨ᴹᶠ[f] p) := by
  induction d <;> try {simp_all [Satisfies];}
  case maxm p ih =>
    let ⟨_, ⟨_, hq⟩⟩ := ih; rw [←hq];
    apply axiomK;
  case disj₃ p q r =>
    simp only [hΓ, FrameConsequence, Satisfies.imp_def];
    intro V w _ hpr hqr hpq;
    simp only [Satisfies.or_def] at hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;

theorem LogicK.Hilbert.sounds {p : Formula α} (f : Frame β) (h : ⊢ᴹ(𝐊) p) : (⊧ᴹᶠ[f] p) := by
  exact (show (⊢ᴹ(𝐊) p) → (⊧ᴹᶠ[f] p) by simpa [Context.box_empty] using sounds' ∅ rfl p f;) h;

theorem LogicK.Hilbert.consistency {f : Frame β} : (⊬ᴹ(𝐊)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ⊧ᴹᶠ[f] (⊥ : Formula α) by exact Frames.bot_def h;
  exact sounds f hC.some;

end LO.Modal.Normal

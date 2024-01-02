import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO.Modal

namespace Hilbert

open Formula FrameConsequence

variable {α β : Type u}

theorem LogicK.sounds' (Γ : Set (Formula α)) (hΓ : Γ = ∅) (p : Formula α) (f : Frame β) (d : Γ ⊢ᴹ(𝐊) p) : (Γ ⊨ᴹᶠ[f] p) := by
  induction d <;> try {simp_all [Satisfies];}
  case wk ih =>
    simp_all only [def_emptyctx];
    exact ih (by aesop);
  case maxm Γ p ih =>
    let ⟨_, ⟨_, hq⟩⟩ := ih; rw [←hq];
    apply preserve_AxiomK;
  case disj₃ p q r =>
    simp only [hΓ, FrameConsequence, Satisfies.imp_def];
    intro V w _ hpr hqr hpq;
    simp only [Satisfies.or_def] at hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;

lemma LogicK.sounds {p : Formula α} (f : Frame β) (h : ⊢ᴹ(𝐊) p) : (⊧ᴹᶠ[f] p) := by
  exact (show (⊢ᴹ(𝐊) p) → (⊧ᴹᶠ[f] p) by simpa [Context.box_empty] using sounds' ∅ rfl p f;) h;

theorem LogicK.unprovable_bot {f : Frame β} : (⊬ᴹ(𝐊)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ⊧ᴹᶠ[f] (⊥ : Formula α) by exact Frames.bot_def h;
  exact sounds f hC.some;

end Hilbert

end LO.Modal

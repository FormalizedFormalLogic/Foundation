import Logic.Modal.Basic.Formula
import Logic.Modal.Basic.HilbertStyle
import Logic.Modal.Basic.Semantics

namespace LO.Modal

namespace Hilbert

open Formula FrameConsequence

variable {α β : Type u}

theorem LogicK.sounds' (Γ : Set (Formula α)) (hΓ : Γ = ∅) (p : Formula α) (f : Frame β) (d : Γ ⊢ᴴ(𝐊) p) : (Γ ⊨ᶠ[f] p) := by
  induction d <;> try {simp_all [satisfies];}
  case wk ih =>
    simp_all only [def_emptyctx];
    exact ih (by aesop);
  case maxm Γ p ih =>
    let ⟨_, ⟨_, hq⟩⟩ := ih; rw [←hq];
    apply preserve_AxiomK;

lemma LogicK.sounds {p : Formula α} (f : Frame β) (h : ⊢ᴴ(𝐊) p) : (⊧ᶠ[f] p) := by
  exact (show (⊢ᴴ(𝐊) p) → (⊧ᶠ[f] p) by simpa [Context.box_empty] using sounds' ∅ rfl p f;) h;

theorem LogicK.unprovable_bot {f : Frame β} : (⊬ᴴ(𝐊)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ⊧ᶠ[f] (⊥ : Formula α) by exact frames.bot_def h;
  exact sounds f hC.some;

end Hilbert

end LO.Modal

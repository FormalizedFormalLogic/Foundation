import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Formula FrameConsequence

variable {α β : Type u} [Inhabited β]
variable (Λ : Logic (Formula α)) [hΛ : LogicDefines β Λ]

/-
  TODO: より一般にこの形で証明できる事実ではないだろうか？
  [LogicK.Hilbert Bew] (Γ : Set (Formula α)) (hΓ : Γ = ∅) (p : Formula α) (f : Frame β) (d : Bew Γ p) : (Γ ⊨ᴹᶠ[f] p)
-/
lemma Logic.Hilbert.sounds
  (Λ : Logic (Formula α)) [hΛ : LogicDefines β Λ]
  (p : Formula α)
  (f : Frame β) (hf : LogicDefines.definability Λ f.rel)
  (d : ⊢ᴹ(Λ) p) : (⊧ᴹᶠ[f] p) := by
  induction d <;> try {simp_all [Satisfies];}
  case maxm p ih =>
    exact (hΛ.defines f).mp hf p ih;
  case disj₃ p q r =>
    simp only [Frames, Models, Satisfies.imp_def];
    intro V w hpr hqr hpq;
    simp only [Satisfies.or_def] at hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;
  /-
  case necessitation p dp ih =>
    simp only [FrameConsequence, Satisfies.box_def];
    intro V w hΓ w' rww';
    apply ih V w';
    intro q hq;
    exact hw rww' (hΓ q hq);
  -/

lemma Logic.Hilbert.consistent
  (β) [Inhabited β]
  (Λ : Logic (Formula α)) [hΛ : LogicDefines β Λ]
  : (⊬ᴹ(Λ)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ∃ (f : Frame β), ⊧ᴹᶠ[f] (⊥ : Formula α) by
    let ⟨f, hf⟩ := h;
    exact Frames.bot_def hf;
  have ⟨tf, htf⟩ := hΛ.trivial_frame;
  existsi tf; exact Logic.Hilbert.sounds Λ ⊥ tf htf hC.some;

theorem LogicK.Hilbert.sounds {p : Formula α} (f : Frame β) (hf : (@LogicK.defines β α).definability f.rel)
  : (⊢ᴹ(𝐊) p) → (⊧ᴹᶠ[f] p) := by
  exact Logic.Hilbert.sounds 𝐊 p f hf;

theorem LogicK.Hilbert.consistency : ⊬ᴹ(𝐊)! (⊥ : Formula α) := Logic.Hilbert.consistent β 𝐊

theorem LogicKD.Hilbert.sounds {p : Formula α} (f : Frame β) (hf : (@LogicKD.defines β α).definability f.rel)
  (h : ⊢ᴹ(𝐊𝐃) p) : (⊧ᴹᶠ[f] p) := by
  exact Logic.Hilbert.sounds 𝐊𝐃 p f hf h;

theorem LogicKD.Hilbert.consistency : ⊬ᴹ(𝐊𝐃)! (⊥ : Formula α) := Logic.Hilbert.consistent β 𝐊𝐃

end LO.Modal.Normal

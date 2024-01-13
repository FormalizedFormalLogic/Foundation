import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Formula FrameConsequence

variable (α β : Type u)[Inhabited β]

lemma Logic.Hilbert.sounds
  (Λ : AxiomSet α)
  (f : Frame β) (hf : f ∈ (FrameClass β α Λ))
  {p : Formula α}
  (d : ⊢ᴹ(Λ) p) : (⊧ᴹᶠ[f] p) := by
  induction d <;> try {simp_all [Satisfies];}
  case disj₃ p q r =>
    simp only [Frames, Models, Satisfies.imp_def];
    intro V w hpr hqr hpq;
    simp only [Satisfies.or_def] at hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;

lemma Logic.Hilbert.consistent
  (Λ : AxiomSet α)
  (hf : ∃ f, f ∈ (FrameClass β α Λ))
  : (⊬ᴹ(Λ)! (⊥ : Formula α)) := by
  by_contra hC; simp at hC;
  suffices h : ∃ (f : Frame β), ⊧ᴹᶠ[f] (⊥ : Formula α) by
    let ⟨f, hf⟩ := h;
    exact Frames.bot_def hf;
  have ⟨tf, htf⟩ := hf;
  existsi tf;
  exact Logic.Hilbert.sounds _ _ Λ tf htf hC.some;

variable {α β : Type u} [Inhabited α] [Inhabited β] {p : Formula α} (f : Frame β)

theorem LogicK.Hilbert.sounds : (⊢ᴹ(𝐊) p) → (⊧ᴹᶠ[f] p) := Logic.Hilbert.sounds _ _ 𝐊 f (def_FrameClass f)
theorem LogicK.Hilbert.consistency : ⊬ᴹ(𝐊)! (⊥ : Formula α) := Logic.Hilbert.consistent α β 𝐊 trivialFrame

theorem LogicKD.Hilbert.sounds (hf : Serial f) (h : ⊢ᴹ(𝐊𝐃) p) : (⊧ᴹᶠ[f] p) := Logic.Hilbert.sounds _ _ 𝐊𝐃 f ((def_FrameClass f).mp hf) h
theorem LogicKD.Hilbert.consistency : ⊬ᴹ(𝐊𝐃)! (⊥ : Formula α) := Logic.Hilbert.consistent α β 𝐊𝐃 trivialFrame

theorem LogicS4.Hilbert.sounds (hf : Reflexive f ∧ Transitive f) (h : ⊢ᴹ(𝐒𝟒) p) : (⊧ᴹᶠ[f] p) := Logic.Hilbert.sounds _ _ 𝐒𝟒 f ((def_FrameClass f).mp hf) h
theorem LogicS4.Hilbert.consistency : ⊬ᴹ(𝐒𝟒)! (⊥ : Formula α) := Logic.Hilbert.consistent α β 𝐒𝟒 trivialFrame

theorem LogicS5.Hilbert.sounds (hf : Reflexive f ∧ Euclidean f) (h : ⊢ᴹ(𝐒𝟓) p) : (⊧ᴹᶠ[f] p) := Logic.Hilbert.sounds _ _ 𝐒𝟓 f ((def_FrameClass f).mp hf) h
theorem LogicS5.Hilbert.consistency : ⊬ᴹ(𝐒𝟓)! (⊥ : Formula α) := Logic.Hilbert.consistent α β 𝐒𝟓 trivialFrame

end LO.Modal.Normal

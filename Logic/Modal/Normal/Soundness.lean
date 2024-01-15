import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Formula

variable (α β : Type u) [DecidableEq α] [Inhabited β]

def AxiomSet.Consistent {α} (Λ : AxiomSet α) := ⊬ᴹ[Λ]! ⊥

open AxiomSet

lemma AxiomSet.sounds
  (Λ : AxiomSet α)
  (f : Frame β) (hf : f ∈ (FrameClass β α Λ))
  {p : Formula α}
  (d : ⊢ᴹ[Λ] p) : (⊧ᴹᶠ[f] p) := by
  induction d <;> try {simp_all [Satisfies];}
  case disj₃ p q r =>
    simp only [Frames, Models, Satisfies.imp_def];
    intro V w hpr hqr hpq;
    simp only [Satisfies.or_def] at hpq;
    cases hpq with
    | inl hp => exact hpr hp;
    | inr hq => exact hqr hq;

lemma AxiomSet.consistent
  (Λ : AxiomSet α)
  (hf : ∃ f, f ∈ (FrameClass β α Λ))
  : Consistent Λ := by
  by_contra hC; simp [Consistent] at hC;
  suffices h : ∃ (f : Frame β), ⊧ᴹᶠ[f] (⊥ : Formula α) by
    let ⟨f, hf⟩ := h;
    exact Frames.bot_def hf;
  have ⟨tf, htf⟩ := hf;
  existsi tf;
  exact AxiomSet.sounds _ _ Λ tf htf hC.some;


variable {α β : Type u} [Inhabited α] [DecidableEq α] [Inhabited β] {p : Formula α} (f : Frame β)

theorem LogicK.sounds : (⊢ᴹ[𝐊] p) → (⊧ᴹᶠ[f] p) := AxiomSet.sounds _ _ 𝐊 f (def_FrameClass f)
theorem LogicK.consistent : Consistent (𝐊 : AxiomSet α) := AxiomSet.consistent α β 𝐊 trivialFrame

theorem LogicKD.sounds (hf : Serial f) (h : ⊢ᴹ[𝐊𝐃] p) : (⊧ᴹᶠ[f] p) := AxiomSet.sounds _ _ 𝐊𝐃 f ((def_FrameClass f).mp hf) h
theorem LogicKD.consistency : Consistent (𝐊𝐃 : AxiomSet α) := AxiomSet.consistent α β 𝐊𝐃 trivialFrame

theorem LogicS4.sounds (hf : Reflexive f ∧ Transitive f) (h : ⊢ᴹ[𝐒𝟒] p) : (⊧ᴹᶠ[f] p) := AxiomSet.sounds _ _ 𝐒𝟒 f ((def_FrameClass f).mp hf) h
theorem LogicS4.consistency : Consistent (𝐒𝟒 : AxiomSet α) := AxiomSet.consistent α β 𝐒𝟒 trivialFrame

theorem LogicS5.sounds (hf : Reflexive f ∧ Euclidean f) (h : ⊢ᴹ[𝐒𝟓] p) : (⊧ᴹᶠ[f] p) := AxiomSet.sounds _ _ 𝐒𝟓 f ((def_FrameClass f).mp hf) h
theorem LogicS5.consistency : Consistent (𝐒𝟓 : AxiomSet α) := AxiomSet.consistent α β 𝐒𝟓 trivialFrame

end LO.Modal.Normal

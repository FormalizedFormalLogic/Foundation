import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

attribute [simp] Finset.union_eq_empty

namespace LO.Modal.Normal

open Formula

variable {α β} [Inhabited α] [DecidableEq α] [Inhabited β]

@[simp]
def AxiomSet.Consistent (Λ : AxiomSet α) := ⊬ᴹ[Λ]! ⊥

open AxiomSet

variable {Λ : AxiomSet α} {p : Formula α}

private lemma AxiomSet.sounds' (Γ : Context α) (_ : Γ = ∅) (h : Deducible Λ Γ p) : (⊧ᴹ[(𝔽(Λ) : FrameClass β)] p) := by
  induction h.some <;> try { simp [FrameClasses, Frames, Models]; try intros; aesop; }
  case modus_ponens h₁ h₂ ih₁ ih₂ he => exact FrameClasses.modus_ponens (ih₁ (by aesop) ⟨h₁⟩) (ih₂ (by aesop) ⟨h₂⟩);

lemma AxiomSet.sounds (h : ⊢ᴹ[Λ]! p) : (⊧ᴹ[(𝔽(Λ) : FrameClass β)] p) := AxiomSet.sounds' ∅ rfl h

lemma AxiomSet.consistent (β) [Inhabited β] [h : Nonempty (𝔽(Λ) : FrameClass β)] : Consistent Λ := by
  by_contra hC; simp at hC;
  suffices h : ∃ (F : Frame β), ⊧ᴹ[F] (⊥ : Formula α) by aesop;
  have ⟨tf, htf⟩ := h.some;
  existsi tf;
  apply AxiomSet.sounds hC;
  assumption;

theorem LogicK.sounds : (⊢ᴹ[𝐊]! p) → (⊧ᴹ[(𝔽((𝐊 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicK.consistent : Consistent (𝐊 : AxiomSet α) := AxiomSet.consistent β

theorem LogicKD.sounds : (⊢ᴹ[𝐊𝐃]! p) → (⊧ᴹ[(𝔽((𝐊𝐃 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicKD.consistent : Consistent (𝐊𝐃 : AxiomSet α) := AxiomSet.consistent β

theorem LogicS4.sounds : (⊢ᴹ[𝐒𝟒]! p) → (⊧ᴹ[(𝔽((𝐒𝟒 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicS4.consistent : Consistent (𝐒𝟒 : AxiomSet α) := AxiomSet.consistent β

theorem LogicS5.sounds : (⊢ᴹ[𝐒𝟓]! p) → (⊧ᴹ[(𝔽((𝐒𝟓 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicS5.consistent : Consistent (𝐒𝟓 : AxiomSet α) := AxiomSet.consistent β

/-
theorem LogicGL.sounds (hf : NonInfiniteAscent f) (h : ⊢ᴹ[𝐆𝐋] p) : (⊧ᴹ[f] p) := AxiomSet.sounds _ _ _ f ((def_FrameClass f).mp hf) h
theorem LogicGL.consistent : Consistent (𝐆𝐋 : AxiomSet α) := AxiomSet.consistent α β _ trivialFrame
-/

end LO.Modal.Normal

import Logic.Modal.Normal.Formula
import Logic.Modal.Normal.HilbertStyle
import Logic.Modal.Normal.Semantics

namespace LO.Modal.Normal

open Formula

@[simp]
def AxiomSet.Consistent {α} (Λ : AxiomSet α) := ⊬ᴹ[Λ]! ⊥

open AxiomSet

variable {α β} [Inhabited α] [Inhabited β] {Λ : AxiomSet α} {p : Formula α}

lemma AxiomSet.sounds (h : ⊢ᴹ[Λ] p) : (⊧ᴹ[(𝔽(Λ) : FrameClass β)] p) := by
  induction h <;> try { simp [FrameClasses, Frames, Models]; try intros; aesop; }
  case modus_ponens ih₁ ih₂ => exact FrameClasses.modus_ponens ih₁ ih₂;

lemma AxiomSet.consistent (hf : ∃ (F : Frame β), F ∈ 𝔽(Λ)) : Consistent Λ := by
  by_contra hC; simp at hC;
  suffices h : ∃ (F : Frame β), ⊧ᴹ[F] (⊥ : Formula α) by aesop;
  have ⟨tf, htf⟩ := hf;
  existsi tf;
  apply AxiomSet.sounds hC.some;
  assumption;

theorem LogicK.sounds : (⊢ᴹ[𝐊] p) → (⊧ᴹ[(𝔽((𝐊 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicK.consistent : Consistent (𝐊 : AxiomSet α) := @AxiomSet.consistent α β _ _ trivialFrame

theorem LogicKD.sounds : (⊢ᴹ[𝐊𝐃] p) → (⊧ᴹ[(𝔽((𝐊𝐃 : AxiomSet α)) : FrameClass β)] p) := by apply AxiomSet.sounds;
theorem LogicKD.consistent : Consistent (𝐊𝐃 : AxiomSet α) := @AxiomSet.consistent α β _ _ trivialFrame

theorem LogicS4.sounds : (⊢ᴹ[𝐒𝟒] p) → (⊧ᴹ[(𝔽((𝐒𝟒 : AxiomSet α)) : FrameClass β)] p)  := by apply AxiomSet.sounds;
theorem LogicS4.consistent : Consistent (𝐒𝟒 : AxiomSet α) := @AxiomSet.consistent α β _ _ trivialFrame

theorem LogicS5.sounds : (⊢ᴹ[𝐒𝟓] p) → (⊧ᴹ[(𝔽((𝐒𝟓 : AxiomSet α)) : FrameClass β)] p)  := by apply AxiomSet.sounds;
theorem LogicS5.consistent : Consistent (𝐒𝟓 : AxiomSet α) := @AxiomSet.consistent α β _ _ trivialFrame

/-
theorem LogicGL.sounds (hf : NonInfiniteAscent f) (h : ⊢ᴹ[𝐆𝐋] p) : (⊧ᴹ[f] p) := AxiomSet.sounds _ _ _ f ((def_FrameClass f).mp hf) h
theorem LogicGL.consistent : Consistent (𝐆𝐋 : AxiomSet α) := AxiomSet.consistent α β _ trivialFrame
-/

end LO.Modal.Normal

import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Deduction

attribute [simp] Finset.union_eq_empty

namespace LO.Modal.Normal

open Formula

variable {α β} [Inhabited α] [DecidableEq α]

@[simp] def AxiomSet.Consistent (Λ : AxiomSet α) := ⊬ᴹ[Λ]! ⊥

open AxiomSet

variable {Λ : AxiomSet α} {p : Formula α}

open FrameClasses in
private lemma AxiomSet.soundsAux {Γ : Theory α} (hΓ : Γ = ∅) (d : Γ ⊢ᴹ[Λ]! p) : (⊧ᴹ[(𝔽(Λ) : FrameClass β)] p) := by
  induction d.some with
  | axm => subst hΓ; contradiction;
  | maxm => intros _ hF _ _; apply hF; simpa;
  | modus_ponens h₁ h₂ ih₁ ih₂ => exact modus_ponens (ih₁ (by simp_all) ⟨h₁⟩) (ih₂ (by simp_all) ⟨h₂⟩);
  | necessitation h ih => exact necessitation (ih rfl ⟨h⟩);
  | verum => exact verum;
  | imply₁ => exact imply₁;
  | imply₂ => exact imply₂;
  | conj₁ => exact conj₁;
  | conj₂ => exact conj₂;
  | conj₃ => exact conj₃;
  | disj₁ => exact disj₁;
  | disj₂ => exact disj₂;
  | disj₃ => exact disj₃;
  | dne => exact dne;

theorem AxiomSet.sounds (d : ⊢ᴹ[Λ]! p) : (⊧ᴹ[(𝔽(Λ) : FrameClass β)] p) := AxiomSet.soundsAux rfl d

theorem AxiomSet.ssounds (d : Γ ⊢ᴹ[Λ]! p) : (Γ ⊨ᴹ[(𝔽(Λ) : FrameClass β)] p) := by
  obtain ⟨Δ, ⟨sΔ, dΔ⟩⟩ := d.compact;
  have h₂ : ⊧ᴹ[(𝔽(Λ) : FrameClass β)] (Δ.conj ⟶ p) := AxiomSet.sounds $ Deducible.dtr_strong dΔ;
  intro F hF V w hΓ;
  simp [FrameClasses, Frames, Models] at h₂;
  exact h₂ F hF V w (Theory.satisfies_conj sΔ hΓ);

section

lemma AxiomSet.consistent (β) [Inhabited β] [h : Nonempty (𝔽(Λ) : FrameClass β)] : Consistent Λ := by
  by_contra hC;
  suffices h : ∃ (F : Frame β), ⊧ᴹ[F] (⊥ : Formula α) by simp_all;
  obtain ⟨F, hF⟩ := h.some;
  existsi F;
  apply AxiomSet.sounds (by simpa using hC);
  simpa;

variable [Inhabited β]

theorem LogicK.consistent : Consistent (𝐊 : AxiomSet α) := AxiomSet.consistent β
theorem LogicKD.consistent : Consistent (𝐊𝐃 : AxiomSet α) := AxiomSet.consistent β
theorem LogicS4.consistent : Consistent (𝐒𝟒 : AxiomSet α) := AxiomSet.consistent β
theorem LogicS5.consistent : Consistent (𝐒𝟓 : AxiomSet α) := AxiomSet.consistent β

end LO.Modal.Normal

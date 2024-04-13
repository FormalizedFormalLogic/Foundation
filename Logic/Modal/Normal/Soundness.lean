import Logic.Modal.Normal.Semantics
import Logic.Modal.Normal.Deduction

attribute [simp] Finset.union_eq_empty

namespace LO.Modal.Normal

open Formula

variable {α β} [Inhabited α] [DecidableEq α]

@[simp] def AxiomSet.Consistent (Λ : AxiomSet α) := ∅ ⊬ᴹ[Λ]! ⊥

open AxiomSet

variable {Λ : AxiomSet α} {p : Formula α}

theorem AxiomSet.sounds (d : Γ ⊢ᴹ[Λ]! p) : (Γ ⊨ᴹ[(𝔽(Λ) : FrameClass β)] p) := by
  induction d.some with
  | axm h => intro _ _ _ _ hΓ; exact hΓ _ h;
  | maxm h => intro _ hF _ _ _; apply hF; simpa;
  | @modus_ponens Γ₁ Γ₂ p q h₁ h₂ ih₁ ih₂ =>
    have hpq := FrameClassConsequence.weakening (show Γ₁ ⊆ (Γ₁ ∪ Γ₂) by simp) $ ih₁ ⟨h₁⟩;
    have hp := FrameClassConsequence.weakening (show Γ₂ ⊆ (Γ₁ ∪ Γ₂) by simp) $ ih₂ ⟨h₂⟩;
    exact FrameClassConsequence.modus_ponens' hpq hp;
  | necessitation h ih =>
    have := ih ⟨h⟩;
    exact FrameClassConsequence.necessitation _ this
  | _ =>
    simp only [FrameClassConsequence, FrameConsequence];
    intros;
    try first
    | apply Models.verum;
    | apply Models.imply₁;
    | apply Models.imply₂;
    | apply Models.conj₁;
    | apply Models.conj₂;
    | apply Models.conj₃;
    | apply Models.disj₁;
    | apply Models.disj₂;
    | apply Models.disj₃;
    | apply Models.dne;

lemma AxiomSet.consistent (β) [Inhabited β] [h : Nonempty (𝔽(Λ) : FrameClass β)] : Consistent Λ := by
  intro h;
  have : ∅ ⊨ᴹ[(𝔽(Λ) : FrameClass β)] ⊥ := AxiomSet.sounds h;
  simp_all [FrameClassConsequence, FrameConsequence]

/-
variable [Inhabited β]

theorem LogicK.consistent : Consistent (𝐊 : AxiomSet α) := AxiomSet.consistent β
theorem LogicKD.consistent : Consistent (𝐊𝐃 : AxiomSet α) := AxiomSet.consistent β
theorem LogicS4.consistent : Consistent (𝐒𝟒 : AxiomSet α) := AxiomSet.consistent β
theorem LogicS5.consistent : Consistent (𝐒𝟓 : AxiomSet α) := AxiomSet.consistent β
-/

end LO.Modal.Normal

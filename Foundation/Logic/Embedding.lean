module

public import Foundation.Propositional.Entailment.Cl

@[expose] public section

/-! # Faithful embeddings among logical systems -/

namespace LO.Entailment

variable {F₁ F₂ F₃ : Type*} {S₁ S₂ S₃ : Type*} [Entailment S₁ F₁] [Entailment S₂ F₂] [Entailment S₃ F₃]

def IsFaithfulEmbedding (𝓢₁ : S₁) (𝓢₂ : S₂) (f : F₁ → F₂) : Prop := ∀ φ, 𝓢₂ ⊢ f φ ↔ 𝓢₁ ⊢ φ

class FaithfullyEmbeddable (𝓢₁ : S₁) (𝓢₂ : S₂) : Prop where
  prop : ∃ f : F₁ → F₂, IsFaithfulEmbedding 𝓢₁ 𝓢₂ f

namespace FaithfullyEmbeddable

lemma fun_exists (𝓢₁ : S₁) (𝓢₂ : S₂) [FaithfullyEmbeddable 𝓢₁ 𝓢₂] :
    ∃ f : F₁ → F₂, IsFaithfulEmbedding 𝓢₁ 𝓢₂ f := FaithfullyEmbeddable.prop

@[refl] protected instance refl (𝓢₁ : S₁) : FaithfullyEmbeddable 𝓢₁ 𝓢₁ where
  prop := ⟨id, by intros _; simp⟩

@[trans] lemma trans (𝓢₁ : S₁) (𝓢₂ : S₂) (𝓢₃ : S₃) [FaithfullyEmbeddable 𝓢₁ 𝓢₂] [FaithfullyEmbeddable 𝓢₂ 𝓢₃] :
    FaithfullyEmbeddable 𝓢₁ 𝓢₃ where
  prop := by
    rcases fun_exists 𝓢₁ 𝓢₂ with ⟨f₁₂, h₁₂⟩
    rcases fun_exists 𝓢₂ 𝓢₃ with ⟨f₂₃, h₂₃⟩
    refine ⟨f₂₃ ∘ f₁₂, ?_⟩
    intro φ; simp [h₁₂ φ, h₂₃ (f₁₂ φ)]

end FaithfullyEmbeddable

end LO.Entailment

end

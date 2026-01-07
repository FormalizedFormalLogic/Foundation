import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Theory of first-order logic

First-order theory `Theory L` is defined as a set of sentence.
-/

namespace LO.FirstOrder

/-! Schema is a set of formulas closed under term substitution. -/
structure Schema (L : Language) where
  val : Set (SyntacticFormula L)
  rewrite_closed : ∀ φ ∈ val, ∀ f : ℕ → SyntacticTerm L, Rew.rewrite f ▹ φ ∈ val

namespace Schema

instance : SetLike (Schema L) (SyntacticFormula L) where
  coe s := s.val
  coe_injective' s₁ s₂ h := by cases s₁; cases s₂; congr

def closure (s : Set (SyntacticFormula L)) : Schema L where
  val := { φ | ∃ ψ ∈ s, ∃ f : ℕ → SyntacticTerm L, φ = Rew.rewrite f ▹ ψ }
  rewrite_closed := by
    rintro φ ⟨ψ, hψ, f, rfl⟩ g
    simpa [←TransitiveRewriting.comp_app, Rew.rewrite_comp_rewrite]
      using ⟨ψ, hψ, Rew.rewrite g ∘ f, rfl⟩

instance : AdjunctiveSet (SyntacticFormula L) (Schema L) where
  Subset 𝔖 𝔗 := 𝔖 ≤ 𝔗
  emptyCollection := ⟨∅, by simp⟩
  adjoin φ 𝔖 := by {  }

end Schema

/--/
abbrev Theory (L : Language) := Set (Sentence L)

instance : AdjunctiveSet (SyntacticFormula L) (SyntacticFormulas L) := inferInstance

instance : AdjunctiveSet (Sentence L) (Theory L) := inferInstance

namespace Theory

variable (T U : Theory L)

def lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T

variable {T U}

instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩

lemma add_def : T + U = T ∪ U := rfl

@[coe] def toSyntacticFormulas (T : Theory L) : SyntacticFormulas L := Rewriting.emb '' T

instance : Coe (Theory L) (SyntacticFormulas L) := ⟨toSyntacticFormulas⟩

@[simp] lemma coe_mem_coe {σ : Sentence L} {T : Theory L} : (σ : SyntacticFormula L) ∈ (T : SyntacticFormulas L) ↔ σ ∈ T := by
  simp [toSyntacticFormulas]

@[simp] lemma coe_empty_eq : ((∅ : Theory L) : SyntacticFormulas L) = ∅ := by simp [toSyntacticFormulas]

@[simp] lemma coe_subset_coe : (T : SyntacticFormulas L) ⊆ (U : SyntacticFormulas L) ↔ T ⊆ U := by
  constructor
  · intro h σ hσ
    simpa using h (Theory.coe_mem_coe.mpr hσ)
  · simp only [toSyntacticFormulas, Set.image_subset_iff]
    intro h σ hσ
    refine Set.mem_preimage.mpr (Theory.coe_mem_coe.mpr (h hσ))

@[simp] lemma coe_insert (σ : Sentence L) (T : Theory L) : (insert σ T).toSyntacticFormulas = insert ↑σ ↑T := by
  ext; simp [toSyntacticFormulas]; tauto

end Theory

namespace SyntacticFormulas

def lMap (Φ : L₁ →ᵥ L₂) (𝔖 : SyntacticFormulas L₁) : SyntacticFormulas L₂ := Semiformula.lMap Φ '' 𝔖

@[coe] def toTheory (𝔖 : SyntacticFormulas L) : Theory L := Semiformula.univCl '' 𝔖

instance : CoeOut (SyntacticFormulas L) (Theory L) := ⟨toTheory⟩

end SyntacticFormulas

@[simp] lemma Theory.coe_insert_eq (σ : Sentence L) (𝔖 : SyntacticFormulas L) :
    ((insert ↑σ 𝔖 : SyntacticFormulas L) : Theory L) = insert σ ↑𝔖 := by
  ext τ
  simp [SyntacticFormulas.toTheory]
  simp [Semiformula.univCl]
  tauto

abbrev ArithmeticAxiom := Theory ℒₒᵣ



end LO.FirstOrder

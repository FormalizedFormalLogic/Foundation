import Foundation.FirstOrder.Basic.Syntax.Rew

/-!
# Theory of first-order logic

First-order theory `Theory L` is defined as a set of sentence.
-/

namespace LO.FirstOrder

abbrev Schema (L : Language) := Set (SyntacticFormula L)

abbrev Theory (L : Language) := Set (Sentence L)

instance : AdjunctiveSet (SyntacticFormula L) (Schema L) := inferInstance

instance : AdjunctiveSet (Sentence L) (Theory L) := inferInstance

namespace Theory

variable (T U : Theory L)

def lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T

variable {T U}

instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩

lemma add_def : T + U = T ∪ U := rfl

@[coe] def toSchema (T : Theory L) : Schema L := Rewriting.emb '' T

instance : Coe (Theory L) (Schema L) := ⟨toSchema⟩

@[simp] lemma coe_mem_coe {σ : Sentence L} {T : Theory L} : (σ : SyntacticFormula L) ∈ (T : Schema L) ↔ σ ∈ T := by
  simp [toSchema]

@[simp] lemma coe_empty_eq : ((∅ : Theory L) : Schema L) = ∅ := by simp [toSchema]

@[simp] lemma coe_subset_coe : (T : Schema L) ⊆ (U : Schema L) ↔ T ⊆ U := by
  constructor
  · intro h σ hσ
    simpa using h (Theory.coe_mem_coe.mpr hσ)
  · simp only [toSchema, Set.image_subset_iff]
    intro h σ hσ
    refine Set.mem_preimage.mpr (Theory.coe_mem_coe.mpr (h hσ))

@[simp] lemma coe_insert (σ : Sentence L) (T : Theory L) : (insert σ T).toSchema = insert ↑σ ↑T := by
  ext; simp [toSchema]; tauto

end Theory

namespace Schema

def lMap (Φ : L₁ →ᵥ L₂) (𝓢 : Schema L₁) : Schema L₂ := Semiformula.lMap Φ '' 𝓢

@[coe] def toTheory (𝓢 : Schema L) : Theory L := Semiformula.univCl '' 𝓢

instance : CoeOut (Schema L) (Theory L) := ⟨toTheory⟩

end Schema

@[simp] lemma Theory.coe_insert_eq (σ : Sentence L) (𝓢 : Schema L) :
    ((insert ↑σ 𝓢 : Schema L) : Theory L) = insert σ ↑𝓢 := by
  ext τ
  simp [Schema.toTheory]
  simp [Semiformula.univCl]
  tauto

abbrev ArithmeticAxiom := Theory ℒₒᵣ

end LO.FirstOrder

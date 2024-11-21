import Logic.Logic.Calculus

namespace LO

class FiniteInferenceRule (S : outParam Type*) (Rule : Type*) where
  genProp : Rule → S → Prop
  genSeq {ρ : Rule} {Γ : S} : genProp ρ Γ → List S

variable {F : Type*} [LogicalConnective F] {Rule : Type*} [FiniteInferenceRule (List F) Rule]

inductive FiniteInferenceRule.Tree : List F → Type _
  | inference {ρ : Rule} {Γ : List F} (h : FiniteInferenceRule.genProp ρ Γ) :
    (Π Δ ∈ FiniteInferenceRule.genSeq h, Tree Δ) → Tree Γ

inductive FiniteInferenceRule.TreeWithCut : List F → Type _
  | inference {ρ : Rule} {Γ : List F} (h : FiniteInferenceRule.genProp ρ Γ) :
      (Π Δ ∈ FiniteInferenceRule.genSeq h, TreeWithCut Δ) → TreeWithCut Γ
  | cut {Γ : List F} {p : F} : TreeWithCut (p :: Γ) → TreeWithCut (∼p :: Γ) → TreeWithCut Γ

namespace FiniteInferenceRule

local prefix:60 "⊢⁰ " => Tree

local prefix:60 "⊢ᶜ " => TreeWithCut




end FiniteInferenceRule


end LO

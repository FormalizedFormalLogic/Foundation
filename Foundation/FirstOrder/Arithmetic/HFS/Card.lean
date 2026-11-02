module

public import Foundation.FirstOrder.Arithmetic.HFS.Basic

@[expose] public section
/-!

# Cardinality of hereditarily finite sets

-/

namespace FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def CardLE (a b : V) : Prop :=
  ∃ f, IsMapping.IsFunction f ∧ IsMapping.Injective f ∧ domain f = a ∧ range f ⊆ b

scoped infix:50 " ≤# " => CardLE

#check IsMapping.injectiveDef

def CardLE.dfn : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  -- (.mkSigma “a b. ∃ p, !exponentialDef (a + b) p ∧ ∃ f < p, ∃ r <⁺ 2 * f,
  --   !IsMapping.isFunctionDef f ∧ !IsMapping.injectiveDef f ∧
  --   !domainDef a f ∧ !rangeDef r f ∧ !bitSubsetDef r b”)
  -- (.mkPi “a b. ∀ p, !exponentialDef (a + b) p → ∃ f < p, ∃ r <⁺ 2 * f,
  --   !IsMapping.isFunctionDef f ∧ !IsMapping.injectiveDef f ∧
  --   !domainDef a f ∧ !rangeDef r f ∧ !bitSubsetDef r b”)
  (.mkSigma “a b. ∃ p, !exponentialDef (a + b + 1)² p ∧ ∃ f < p, ∃ r <⁺ 2 * f,
    !IsMapping.isFunctionDef f ∧ !IsMapping.injectiveDef f ∧
    !domainDef a f ∧ !rangeDef r f ∧ !bitSubsetDef r b”)
  (.mkPi “a b. ∀ p, !exponentialDef (a + b + 1)² p → ∃ f < p, ∃ r <⁺ 2 * f,
    !IsMapping.isFunctionDef f ∧ !IsMapping.injectiveDef f ∧
    !domainDef a f ∧ !rangeDef r f ∧ !bitSubsetDef r b”)

set_option linter.flexible false in
lemma CardLE.defined : 𝚫ᴬ₁-Relation[V] CardLE via CardLE.dfn :=
  ⟨fun v ↦ by
    simp [dfn]
    constructor <;> intro h
    · intro p' hp'
      obtain ⟨p, hp⟩ := h
      exact Exponential.uniq hp.1 hp' ▸ hp.2
    · let p := Exp.exp ((v 0 + v 1 + 1) ^ 2)
      have hp := exponential_exp ((v 0 + v 1 + 1) ^ 2)
      exact ⟨p, hp, (h p) hp⟩,
   fun v ↦ by
    simp [dfn]
    constructor <;> intro h
    · obtain ⟨p, hp, f, hf⟩ := h
      use f
      aesop
    · obtain ⟨f, hf⟩ := h
      let p := Exp.exp ((v 0 + v 1 + 1) ^ 2)
      have hp := exponential_exp ((v 0 + v 1 + 1) ^ 2)
      refine ⟨p, hp, f, ?_, by aesop⟩
      · have hsubset := hf.1.2
        have hexponent : v 0 + range f + 1 ≤ v 0 + v 1 + 1 :=
          add_le_add_three le_rfl (le_of_subset hf.2.2.2) le_rfl
        apply le_of_subset at hsubset
        calc
          f < Exp.exp ((domain f + range f + 1) ^ 2) := lt_of_le_of_lt hsubset product_bound'
          _ = Exp.exp ((v 0 + range f + 1) ^ 2) := by aesop
          _ ≤ Exp.exp ((v 0 + v 1 + 1) ^ 2) := exp_monotone_le.mpr (sq_le_sq.mpr hexponent)⟩

lemma CardLE.definable : 𝚫ᴬ₁-Relation[V] CardLE := CardLE.defined.to_definable

def CardEQ (a b : V) : Prop := CardLE a b ∧ CardLE b a

scoped infix:60 " ≋ " => CardEQ

def CardEQ.dfn : 𝚫ᴬ₁.Semisentence 2 := .mkDelta
  (.mkSigma “a b. !CardLE.dfn.sigma a b ∧ !CardLE.dfn.sigma b a”)
  (.mkPi “a b. !CardLE.dfn.pi a b ∧ !CardLE.dfn.pi b a”)

lemma CardEQ.defined : 𝚫ᴬ₁-Relation[V] CardEQ via CardEQ.dfn :=
  ⟨fun v ↦ by
    simp [CardLE.defined.iff]
    sorry,
   fun v ↦ by
    #check CardLE.defined.iff
    sorry⟩

lemma CardEQ.definable : 𝚫ᴬ₁-Relation[V] CardEQ := CardEQ.defined.to_definable

end FFL.FirstOrder.Arithmetic

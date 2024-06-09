# Syntax and Semantics for Classical Propositional Logic

## Deduction System
  We adupt the Tait-calculus as a deduction system of classical propositional logic.

```lean
  abbrev Sequent (α : Type*) := List (Formula α)
  
  inductive Derivation : Sequent α → Type _
  | axL (Δ a)   : Derivation (Formula.atom a :: Formula.natom a :: Δ)
  | verum (Δ)   : Derivation (⊤ :: Δ)
  | or {Δ p q}  : Derivation (p :: q :: Δ) → Derivation (p ⋎ q :: Δ)
  | and {Δ p q} : Derivation (p :: Δ) → Derivation (q :: Δ) → Derivation (p ⋏ q :: Δ)
  | wk {Δ Γ}    : Derivation Δ → Δ ⊆ Γ → Derivation Γ
  | cut {Δ p}   : Derivation (p :: Δ) → Derivation (~p :: Δ) → Derivation Δ

  instance : OneSided (Formula α) := ⟨Derivation⟩
```
- [LO.Propositional.Classical.Derivation](https://iehality.github.io/lean4-logic/docs/Logic/Propositional/Classical/Basic/Calculus.html#LO.Propositional.Classical.Derivation)

## Semantics

## Soundness and Completeness
  
  The soundness theorem is proved by induction of derivation.
  
  ```lean
    instance (T : Theory α) : Sound T (Semantics.models (Valuation α) T)
  ```
  - [LO.Propositional.Classical.instSoundTheoryFormulaSetValuationModels](https://iehality.github.io/lean4-logic/docs/Logic/Propositional/Classical/Basic/Completeness.html#LO.Propositional.Classical.instSoundTheoryFormulaSetValuationModels)

  The conpleteness theorem is also proved by constructing maximal consistent theory.
  
  ```lean
    instance (T : Theory α) : Complete T (Semantics.models (Valuation α) T)
  ```
  - [LO.Propositional.Classical.instCompleteTheoryFormulaSetValuationModels](https://iehality.github.io/lean4-logic/docs/Logic/Propositional/Classical/Basic/Completeness.html#LO.Propositional.Classical.instCompleteTheoryFormulaSetValuationModels)
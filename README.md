# lean4-logic
Formalizing Logic in Lean4

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Predicate**: Predicate logic
    - **FirstOrder**: First-Order logic
      - **Completeness**: Completeness theorem
      - **Arith**: Arithmetic

## Definition
### First-Order logic

|                            |                                     | Definition                   | Notation |
| :----:                     | ----                                | ----                         | ----     |
| $\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus         |  `FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $T \vdash \sigma$          | Provability, Proof                  |  `FirstOrder.Proof`          | `T ⊢ σ`  |
| $M \models \sigma$         | Tarski's truth definition condition |  `FirstOrder.SubFormula.Val` | `M ⊧₁ σ` |

## Theorem
### First-Order logic

|                                | Proof                     | Proposition      | 
| ----                           |  ----                     | ----             |
| Soundness theorem              | `FirstOrder.soundness`    | `T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `FirstOrder.completeness` | `T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | TODO                      |                  |
| Gödel's incompleteness theorem | TODO                      |                  |

# lean4-logic
Formalizing Logic in Lean4

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Predicate**: Predicate logic
    - **FirstOrder**: First-Order logic
      - **Completeness**: Completeness theorem
      - **Principia**: Proof system
      - **Arith**: Arithmetic

## Definition
### First-Order logic

|                                     |                                     | Definition                   | Notation |
| :----:                              | ----                                | ----                         | :----:   |
| $\vdash_\mathrm{T} \Gamma$          | Derivation in Tait-Calculus         |  `FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `FirstOrder.DerivationCut`     | `⊢ᶜ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `FirstOrder.SubFormula.Val` | `M ⊧₁ σ` |
| $T \vdash \sigma$                   | Provability, Proof                  |  `FirstOrder.Proof`          | `T ⊢ σ`  |
|  | Redundant but practical proof system (`[]⟹[T] emb σ` is equivalent to `T ⊢ σ`) | `FirstOrder.Principia` | `[p₁ p₂ p₃, ...]⟹[T] q` |

## Theorem
### First-Order logic

|                                | Proof                     | Proposition      | 
| ----                           |  ----                     | :----:           |
| Soundness theorem              | `FirstOrder.soundness`    | `T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `FirstOrder.completeness` | `T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | `FirstOrder.DerivationCutRestricted.hauptsatz`    | `⊢ᶜ Δ → ⊢ᵀ Δ`   |
| Gödel's incompleteness theorem | TODO                      |                  |

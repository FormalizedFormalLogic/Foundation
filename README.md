# lean4-logic
Formalizing Logic in Lean4

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Logic**
  - **Propositional**: Propositional logic
  - **Predicate**: Predicate logic
    - **FirstOrder**: First-Order logic
      - **Basic**: Basic definitions & theorems
      - **Computability**: encodeing, computability
      - **Completeness**: Completeness theorem
      - **Arith**: Arithmetic
      - **Incompleteness**: Incompleteness theorem

## Definition
### First-Order logic

|                                     |                                     | Definition                   | Notation |
| :----:                              | ----                                | ----                         | :----:   |
| $\vdash_\mathrm{T} \Gamma$          | Derivation in Tait-Calculus         |  `LO.FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `LO.FirstOrder.DerivationC`     | `⊢ᶜ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.Subformula.Val` | `M ⊧ σ` |
| $T \vdash \sigma$                   | Provability, Proof                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`  |

## Theorem
### First-Order logic

|                                | Proof                     | Proposition      | 
| ----                           |  ----                     | :----:           |
| Soundness theorem              | `LO.FirstOrder.soundness`    | `T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `LO.FirstOrder.completeness` | `T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | `LO.FirstOrder.DerivationCR.hauptsatz`    | `⊢ᶜ Δ → ⊢ᵀ Δ`   |
| Gödel's first incompleteness theorem | `LO.FIrstOrder.Arith.firstIncompleteness` | `SigmaOneSound T → Theory.Computable T → ¬Logic.System.Complete T` |

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
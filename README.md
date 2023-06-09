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

## Theorem
### First-Order logic

|                                | Proof                     | Proposition      | 
| ----                           |  ----                     | :----:           |
| Soundness theorem              | `FirstOrder.soundness`    | `T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `FirstOrder.completeness` | `T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | `FirstOrder.DerivationCutRestricted.hauptsatz`    | `⊢ᶜ Δ → ⊢ᵀ Δ`   |
| Gödel's incompleteness theorem | TODO                      |                  |

## Principia
- Redundant but practical [formal [formal proof system]]
- `[emb σ₁, emb σ₂, ...]⟹[T] emb σ` is equivalent to `T ⊢ σ₁ ∧ σ₂ ∧ ... → σ`

```code:eqZeroOfAddEqZero.lean
def zeroBot : [] ⟹[T] “∀ 0 ≤ #1” :=
  proof.
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as "zero or succ" · from zeroOrSucc
    then ∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1) as "le def" · from leIffEqOrLt
    then ∀ (0 < #0 + 1) as "zero lt succ" · from zeroLtSucc
    generalize
    rewrite 0 ≤ &0 ↔ 0 = &0 ∨ 0 < &0
    @ specialize "le def" with 0, &0
    cases &0 = 0 or ∃ &0 = #0 + 1
    @ specialize "zero or succ" with &0
    · left 
    · right; choose this; rew this; specialize "zero lt succ" with &0
  qed.
```
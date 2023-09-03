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
      - **Completeness**: Completeness theorem
      - **Principia**: Proof system
      - **Arith**: Arithmetic

## Definition
### First-Order logic

|                                     |                                     | Definition                   | Notation |
| :----:                              | ----                                | ----                         | :----:   |
| $\vdash_\mathrm{T} \Gamma$          | Derivation in Tait-Calculus         |  `LO.FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `LO.FirstOrder.DerivationC`     | `⊢ᶜ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.SubFormula.Val` | `M ⊧₁ σ` |
| $T \vdash \sigma$                   | Provability, Proof                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`  |

## Theorem
### First-Order logic

|                                | Proof                     | Proposition      | 
| ----                           |  ----                     | :----:           |
| Soundness theorem              | `LO.FirstOrder.soundness`    | `T ⊢ σ → T ⊨ σ` |
| Completeness theorem           | `LO.FirstOrder.completeness` | `T ⊨ σ → T ⊢ σ` |
| Cut-elimination                | `LO.FirstOrder.DerivationCR.hauptsatz`    | `⊢ᶜ Δ → ⊢ᵀ Δ`   |
| Gödel's incompleteness theorem | TODO                      |                  |

## Principia
- Redundant but practical [formal [formal proof system]]
- `[emb σ₁, emb σ₂, ...]⟹[T] emb σ` is equivalent to `T ⊢ σ₁ ∧ σ₂ ∧ ... → σ`

```code:eqZeroOfMulEqZero.lean
def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∨ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as "succ ne zero" · from succNeZero
    then ∀ (#0 ≠ 0 → ∃ #1 = #0 + 1) as "eq succ of pos" · from zeroOrSucc
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as "add succ" · from addSucc 
    then ∀ ∀ (#0 * (#1 + 1) = (#0 * #1) + #0) as "mul succ" · from mulSucc
    generalize; generalize; intro as "h₀"
    absurd as "ne zero"
    have ∃ &0 = #0 + 1
    · specialize "eq succ of pos" with &0 as "h"
      apply "h"
      · andl "ne zero"
    choose this as "e₁"
    have ∃ &2 = #0 + 1
    · specialize "eq succ of pos" with &2 as "h"
      apply "h"
      · andr "ne zero"
    choose this as "e₂"
    have &2 * &3 = (&1 + 1)*&0 + &1 + 1 as "h₁"
    · specialize "mul succ" with &1 + 1, &0 as "ms"
      specialize "add succ" with (&1 + 1)*&0, &1 as "as"
      rew "e₁", "e₂", "ms", "as"
      rfl
    have (&1 + 1)*&0 + &1 + 1 = 0
    · rew ←"h₁"
    have (&1 + 1)*&0 + &1 + 1 ≠ 0
    · specialize "succ ne zero" with (&1 + 1)*&0 + &1
    contradiction this
  qed.
```
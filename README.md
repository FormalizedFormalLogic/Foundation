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
def eqZeroOfAddEqZero : [] ⟹[T] “∀ ∀ (#0 + #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as "ne zero" · from succNeZero
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as "zero or succ" · from zeroOrSucc
    then ∀ #0 + 0 = #0 as "add zero" · from addZero
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as "add succ" · from addSucc  
    generalize; generalize; intro as "h₀"
    cases &1 = 0 as "h₁" or ∃ &1 = #0 + 1 as "h₁" @ specialize "zero or succ" with &1
    · cases &0 = 0 as "h₂" or ∃ &0 = #0 + 1 as "h₂"
      @ specialize "zero or succ" with &0
      · split
      · choose "h₂" as "h₃"
        have &0 + 1 = 0 as "contra"
        · have &0 + 1 + 0 = 0 · rew ←"h₃", ←"h₁", "h₀"
          rewrite &0 + 1 = &0 + 1 + 0
          @ symmetry; specialize "add zero" with &0 + 1
        have &0 + 1 ≠ 0
        · specialize "ne zero" with &0
        contradiction "contra"
    · choose "h₁" as "h₂"
      have (&1 + &0) + 1 = 0 as "contra"
      · rewrite (&1 + &0) + 1 = &1 + (&0 + 1)
        @ symmetry; specialize "add succ" with &1, &0
        rewrite ←"h₂"
      have (&1 + &0) + 1 ≠ 0 
      · specialize "ne zero" with &1 + &0
      contradiction "contra"
  qed.
```
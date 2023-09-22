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
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.SubFormula.Val` | `M ⊧ σ` |
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
    then ∀ #0 + 1 ≠ 0 as .succ_ne_zero · from succNeZero
    then ∀ (#0 ≠ 0 → ∃ #1 = #0 + 1) as .eq_succ_of_pos · from zeroOrSucc
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as .add_succ · from addSucc 
    then ∀ ∀ (#0 * (#1 + 1) = (#0 * #1) + #0) as .mul_succ · from mulSucc
    generalize m; generalize n; intro as .h₀
    absurd as .ne_zero
    have ∃ n = #0 + 1
    · specialize .eq_succ_of_pos with n as .h
      apply .h
      · andl .ne_zero
    choose n' st this as .hn'
    have ∃ m = #0 + 1
    · specialize .eq_succ_of_pos with m as .h
      apply .h
      · andr .ne_zero
    choose m' st this as .hm'
    have n * m = (n' + 1)*m' + n' + 1 as .h₁
    · specialize .mul_succ with n' + 1, m' as .hms
      specialize .add_succ with (n' + 1)*m', n' as .has
      rw[.hn', .hm', .hms, .has]
      refl
    have (n' + 1)*m' + n' + 1 = 0
    · rw[←.h₁]
    have (n' + 1)*m' + n' + 1 ≠ 0
    · specialize .succ_ne_zero with (n' + 1)*m' + n'
    contradiction this
  qed.
```
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

```code:ltOfLeOfLt.lean
def ltOfLeOfLt : [] ⟹[T] “∀ ∀ ∀ (#0 ≤ #1 ∧ #1 < #2 → #0 < #2)” :=
  proof.
    then (lt_iff) “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” · from leIffEqOrLt
    then (lt_trans) “∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2)” · from ltTrans
    gens n m l; intro h
    have “l = m ∨ l < m”
    · specialize lt_iff with l, m
      rw[←this]
      andl h
    cases (hl) “l = m” or (hl) “l < m”
    · rw[this]
      andr h
    · specialize lt_trans with l, m, n
      apply this
      · split
        @ assumption
        @ andr h
  qed.
```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
# lean4-logic
Formalizing Logic in Lean4

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Logic**
  - **Propositional**: Propositional logic
    - **Basic**
  - **ManySorted**: Many-sorted logic
    - **Basic**
  - **FirstOrder**: First-order logic
    - **Basic**
    - **Computability**: encodeing, computability
    - **Completeness**: Completeness theorem
    - **Arith**: Arithmetic
    - **Incompleteness**: Incompleteness theorem
  - **SecondOrder**: Monadic second-order logic

## Definition
### First-Order logic

|                                     |                                     | Definition                      | Notation  |
| :----:                              | ----                                | ----                            | :----:    |
| $\vdash_\mathrm{T} \Gamma$          | Derivation in Tait-Calculus         |  `LO.FirstOrder.Derivation`     | `⊢ᵀ Γ`    |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `LO.FirstOrder.DerivationC`    | `⊢ᶜ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.Subformula.Val` | `M ⊧ σ`   |
| $T \vdash \sigma$                   | Proof, Provability                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`, `T ⊢! σ` |

## Theorem

The key results are summarised in `Logic/Summary.lean`.

### First-Order logic

- Cut-elimination
```lean
theorem cut_elimination {Δ : Sequent L} : ⊢ᶜ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz
```

- Compactness theorem
```lean
theorem compactness_theorem (T : Theory L) :
    Semantics.Satisfiableₛ T ↔ ∀ T' : Finset (Sentence L), ↑T' ⊆ T → Semantics.Satisfiableₛ (T' : Theory L) :=
  FirstOrder.compactness
```

- Soundness theorem
```lean
theorem soundness_theorem {σ : Sentence L} : T ⊢ σ → T ⊨ σ := FirstOrder.soundness
```

- Completeness theorem
```lean
theorem completeness_theorem {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness
```

- Gödel's first incompleteness theorem
```lean
variable (T : Theory ℒₒᵣ) [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]

theorem first_incompleteness_theorem : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

theorem undecidable_sentence : T ⊬ undecidableSentence T ∧ T ⊬ ~undecidableSentence T :=
  FirstOrder.Arith.undecidable T
```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
# lean4-logic
Formalizing Logic in Lean4

https://iehality.github.io/lean4-logic/

## Structure
- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Logic**
  - **AutoProver**: Automated theorem proving based on proof search
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
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   |  `LO.FirstOrder.DerivationC`    | `⊢¹ Γ`    |
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.Subformula.Val` | `M ⊧ σ`   |
| $T \vdash \sigma$                   | Proof, Provability                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`, `T ⊢! σ` |

## Theorem

The key results are summarised in `Logic/Summary.lean`.

### First-Order logic

- Cut-elimination
```lean
example [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  {Δ : Sequent L} : ⊢¹ Δ → ⊢ᵀ Δ := DerivationCR.hauptsatz
```

- Completeness theorem
```lean
noncomputable example {σ : Sentence L} : T ⊨ σ → T ⊢ σ := FirstOrder.completeness
```

- Gödel's first incompleteness theorem
```lean
variable (T : Theory ℒₒᵣ)
  [DecidablePred T] [EqTheory T] [PAminus T] [SigmaOneSound T] [Theory.Computable T]

example : ¬System.Complete T :=
  FirstOrder.Arith.first_incompleteness T

example : T ⊬ undecidable T ∧ T ⊬ ~undecidable T :=
  FirstOrder.Arith.undecidable T
```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
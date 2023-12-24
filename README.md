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
| $M \models \sigma$                  | Tarski's truth definition condition |  `LO.FirstOrder.Semiformula.Val` | `M ⊧ σ`   |
| $T \vdash \sigma$                   | Proof, Provability                  |  `LO.FirstOrder.Proof`          | `T ⊢ σ`, `T ⊢! σ` |

## Theorem

The key results are summarised in `Logic/Summary.lean`.

### First-Order logic

- [Cut-elimination](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Hauptsatz.html#LO.FirstOrder.DerivationCR.hauptsatz)
  ```lean
  def LO.FirstOrder.DerivationCR.hauptsatz
      {L : LO.FirstOrder.Language}
      [(k : ℕ) → DecidableEq (LO.FirstOrder.Language.Func L k)]
      [(k : ℕ) → DecidableEq (LO.FirstOrder.Language.Rel L k)]
      {Δ : LO.FirstOrder.Sequent L} :
      ⊢¹ Δ → LO.FirstOrder.Derivation Δ
  ```

- [Completeness theorem](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Completeness/Completeness.html#LO.FirstOrder.completeness)
  ```lean
  noncomputable def LO.FirstOrder.completeness
      {L : LO.FirstOrder.Language}
      {T : LO.FirstOrder.Theory L}
      {σ : LO.FirstOrder.Sentence L} :
      T ⊨ σ → T ⊢ σ
  ```

- [Gödel's first incompleteness theorem](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.first_incompleteness)
  ```lean
  theorem LO.FirstOrder.Arith.first_incompleteness
      (T : LO.FirstOrder.Theory ℒₒᵣ)
      [DecidablePred T]
      [LO.FirstOrder.EqTheory T]
      [LO.FirstOrder.Arith.PAminus T]
      [LO.FirstOrder.Arith.SigmaOneSound T]
      [LO.FirstOrder.Theory.Computable T] :
      ¬LO.System.Complete T
  ```
  - [undecidable sentence](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.undecidable)
    ```lean
    theorem LO.FirstOrder.Arith.undecidable
        (T : LO.FirstOrder.Theory ℒₒᵣ)
        [DecidablePred T]
        [LO.FirstOrder.EqTheory T]
        [LO.FirstOrder.Arith.PAminus T]
        [LO.FirstOrder.Arith.SigmaOneSound T]
        [LO.FirstOrder.Theory.Computable T] :
        T ⊬ LO.FirstOrder.Arith.FirstIncompleteness.undecidable T ∧ T ⊬ ~LO.FirstOrder.Arith.FirstIncompleteness.undecidable T
    ```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
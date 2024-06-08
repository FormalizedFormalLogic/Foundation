# lean4-logic

Formalizing Logic in Lean4

- [Book](https://iehality.github.io/lean4-logic/book): Summary of results. **TODO**
- [Full Documentation](https://iehality.github.io/lean4-logic/docs)

## Table of Contents

- [lean4-logic](#lean4-logic)
  - [Table of Contents](#table-of-contents)
  - [Usage](#usage)
  - [Structure](#structure)
  - [Classical Propositional Logic](#classical-propositional-logic)
    - [Definition](#definition)
    - [Theorem](#theorem)
  - [First-Order Logic](#first-order-logic)
    - [Definition](#definition-1)
    - [Theorem](#theorem-1)
  - Non-Classical
    - [Superintuitionistic Logic](https://iehality.github.io/lean4-logic/book/superntuitionistic/index.html): Intuitionistic propositional logic and some variants.
    - [Standard Modal Logic](https://iehality.github.io/lean4-logic/book/standard_modal/index.html): Propositional logic extended modal operators $\Box$ and $\Diamond$.
  - [References](#references)

## Usage
  Add following to `lakefile.lean`.
  ```lean
  require logic from git "https://github.com/iehality/lean4-logic"
  ```

## Structure

The key results are summarised in `Logic/Summary.lean`.

- **Logic**
  - **Vorspiel**: Supplementary definitions and theorems for Mathlib
  - **Logic**
  - **AutoProver**: Automated theorem proving based on proof search
  - **Propositional**: Propositional logic
    - **Classical**: Classical propositional logic
      - **Basic**
    - **Intuitionistic**: Intuitionistic propositional logic
      - **Kriple**: Kripke semantics
  - **FirstOrder**: First-order logic
    - **Basic**
    - **Computability**: encodeing, computability
    - **Completeness**: Completeness theorem
    - **Arith**: Arithmetic
    - **Incompleteness**: Incompleteness theorem
  - **Modal**: Variants of modal logics
    - **Normal**: Normal propositional modal logic

## Classical Propositional Logic

### Definition

|                                     |                                     | Definition                    | Notation |
| :----:                              | ----                                | ----                          | :----:   |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   | [LO.Propositional.Classical.Derivation](https://iehality.github.io/lean4-logic/Logic/Propositional/Classical/Basic/Calculus.html#LO.Propositional.Classical.Derivation) | `⊢¹ Γ`   |
| $v \models p$                       | Tarski's truth definition condition | [LO.Propositional.Classical.semantics](https://iehality.github.io/lean4-logic/Logic/Propositional/Classical/Basic/Semantics.html#LO.Propositional.Classical.semantics) | `v ⊧ p`  |

### Theorem

- [Soundness theorem](https://iehality.github.io/lean4-logic/Logic/Propositional/Classical/Basic/Completeness.html#LO.Propositional.Classical.soundness)
  ```lean
  theorem LO.Propositional.Classical.soundness
    {α : Type u_1}
    {T : LO.Propositional.Theory α}
    {p : LO.Propositional.Formula α} :
    T ⊢ p → T ⊨ p
  ```

- [Completeness theorem](https://iehality.github.io/lean4-logic/Logic/Propositional/Classical/Basic/Completeness.html#LO.Propositional.Classical.completeness)
  ```lean
  noncomputable def LO.Propositional.Classical.completeness
      {α : Type u_1}
      {T : LO.Propositional.Theory α}
      {p : LO.Propositional.Formula α} :
      T ⊨ p → T ⊢ p
  ```

## First-Order Logic

### Definition
|                                     |                                                | Definition                 | Notation |
| :----:                              | ----                                           | ----                       | :----:   |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut              | [LO.FirstOrder.Derivation](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Calculus.html#LO.FirstOrder.Derivation) | `⊢¹ Γ`   |
| $M \models \sigma$                  | Tarski's truth definition condition            | [LO.FirstOrder.Models](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Semantics/Semantics.html#LO.FirstOrder.Models) | `M ⊧ₘ σ` |
| $T \triangleright U$                | Theory interpretation                          | [LO.FirstOrder.TheoryInterpretation](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Interpretation.html#LO.FirstOrder.TheoryInterpretation) | `T ⊳ U` |
| $\mathbf{EQ}$                       | Axiom of equality                              | [LO.FirstOrder.Theory.eqAxiom](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Eq.html#LO.FirstOrder.Theory.eqAxiom) | `𝐄𝐐` |
| $\mathbf{PA^-}$                     | Finitely axiomatized fragment of $\mathbf{PA}$ | [LO.FirstOrder.Arith.Theory.peanoMinus](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.peanoMinus) | `𝐏𝐀⁻` |
| $\mathbf{I}_\mathrm{open}$          | Induction of open formula                      | [LO.FirstOrder.Arith.Theory.iOpen](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.iOpen) | `𝐈open` |
| $\mathbf{I\Sigma}_n$                | Induction of $\Sigma_n$ formula                | [LO.FirstOrder.Arith.Theory.iSigma](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.iSigma) | `𝐈𝚺` |
| $\mathbf{PA}$                       | Peano arithmetic                               | [LO.FirstOrder.Arith.Theory.peano](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.peano) | `𝐏𝐀` |
| $\mathbf{EA}$                       | elementary arithmetic                               | [LO.FirstOrder.Arith.Theory.elementaryArithmetic](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/EA/Basic.html#LO.FirstOrder.Arith.Theory.elementaryArithmetic) | `𝐄𝐀` |

### Theorem

- [Cut-elimination](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Hauptsatz.html#LO.FirstOrder.Derivation.hauptsatz)
  ```lean
  def LO.FirstOrder.Derivation.hauptsatz
      {L : LO.FirstOrder.Language}
      [(k : ℕ) → DecidableEq (LO.FirstOrder.Language.Func L k)]
      [(k : ℕ) → DecidableEq (LO.FirstOrder.Language.Rel L k)]
      {Δ : LO.FirstOrder.Sequent L} :
      ⊢¹ Δ → { d : ⊢¹ Δ // LO.FirstOrder.Derivation.CutFree d }
  ```

- [Soundness theorem](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Soundness.html#LO.FirstOrder.soundness)
  ```lean
  theorem LO.FirstOrder.soundness
      {L : LO.FirstOrder.Language}
      {T : Set (LO.FirstOrder.Sentence L)}
      {σ : LO.FirstOrder.Sentence L} :
      T ⊢ σ → T ⊨ σ
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
      [𝐄𝐐 ≼ T]
      [𝐏𝐀⁻ ≼ T]
      [LO.FirstOrder.Arith.SigmaOneSound T]
      [LO.FirstOrder.Theory.Computable T] :
      ¬LO.System.Complete T
  ```
  - [undecidable sentence](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.undecidable)
    ```lean
    theorem LO.FirstOrder.Arith.undecidable
        (T : LO.FirstOrder.Theory ℒₒᵣ)
        [DecidablePred T]
        [𝐄𝐐 ≼ T]
        [𝐏𝐀⁻ ≼ T]
        [LO.FirstOrder.Arith.SigmaOneSound T]
        [LO.FirstOrder.Theory.Computable T] :
        T ⊬ LO.FirstOrder.Arith.FirstIncompleteness.undecidable T ∧
        T ⊬ ~LO.FirstOrder.Arith.FirstIncompleteness.undecidable T
    ```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
- 菊池 誠 (編者), 『数学における証明と真理 ─ 様相論理と数学基礎論』
- P. Blackburn, M. de Rijke, Y. Venema, "Modal Logic"
- Open Logic Project, ["The Open Logic Text"](https://builds.openlogicproject.org/)
- R. Hakli, S. Negri, "Does the deduction theorem fail for modal logic?"
- G. Boolos, "The Logic of Provability"
- Huayu Guo, Dongheng Chen, Bruno Bentzen, _"Verified completeness in Henkin-style for intuitionistic propositional logic"_
  - https://arxiv.org/abs/2310.01916
  - https://github.com/bbentzen/ipl

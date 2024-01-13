# lean4-logic
Formalizing Logic in Lean4

https://iehality.github.io/lean4-logic/

## Table of Contents

- [lean4-logic](#lean4-logic)
  - [Table of Contents](#table-of-contents)
  - [Structure](#structure)
  - [Propositional Logic](#propositional-logic)
    - [Definition](#definition)
    - [Theorem](#theorem)
  - [First-Order Logic](#first-order-logic)
    - [Definition](#definition-1)
    - [Theorem](#theorem-1)
  - [Normal Modal Logic](#normal-modal-logic)
    - [Definition](#definition-2)
    - [Theorem](#theorem-2)
  - [References](#references)


## Structure

The key results are summarised in `Logic/Summary.lean`.

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
  - **Modal**: Variants of modal logics
    - **Normal**: Normal propositional modal logic

## Propositional Logic

### Definition

|                                     |                                     | Definition                    | Notation |
| :----:                              | ----                                | ----                          | :----:   |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   | [LO.Propositional.Derivation](https://iehality.github.io/lean4-logic/Logic/Propositional/Basic/Calculus.html#LO.Propositional.Derivation) | `⊢¹ Γ`   |
| $v \models p$                       | Tarski's truth definition condition | [LO.Propositional.semantics](https://iehality.github.io/lean4-logic/Logic/Propositional/Basic/Semantics.html#LO.Propositional.semantics) | `v ⊧ p`  |

### Theorem

- [Completeness theorem](https://iehality.github.io/lean4-logic/Logic/Propositional/Basic/Completeness.html#LO.Propositional.completeness)
  ```lean
  noncomputable def LO.Propositional.completeness
      {α : Type u_1}
      {T : LO.Propositional.Theory α}
      {p : LO.Propositional.Formula α} :
      T ⊨ p → T ⊢ p
  ```

## First-Order Logic

### Definition
|                                     |                                     | Definition                 | Notation |
| :----:                              | ----                                | ----                       | :----:   |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut   | [LO.FirstOrder.Derivation](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Calculus.html#LO.FirstOrder.Derivation) | `⊢¹ Γ`   |
| $M \models \sigma$                  | Tarski's truth definition condition | [LO.FirstOrder.Models](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Semantics/Semantics.html#LO.FirstOrder.Models) | `M ⊧ₘ σ` |

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
        T ⊬ LO.FirstOrder.Arith.FirstIncompleteness.undecidable T ∧
        T ⊬ ~LO.FirstOrder.Arith.FirstIncompleteness.undecidable T
    ```


## Normal Modal Logic

### Definition

In this formalization, _(Modal) Logic_ means set of axioms.

| Logic            | Definition                    | Notation | Remarks         |
| :--------------- | ----------------------------- | :------- | --------------- |
| $\mathbf{K}$     | [LO.Modal.Normal.LogicK](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicK) | `𝐊`      |                 |
| $\mathbf{KD}$     | [LO.Modal.Normal.LogicKD](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicKD) | `𝐊𝐃`      |                 |
| $\mathbf{S4}$    | [LO.Modal.Normal.LogicS4](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicS4) | `𝐒𝟒`     | Alias of `𝐊𝐓𝟒`. |
| $\mathbf{S4.2}$  | [LO.Modal.Normal.LogicS4Dot2](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicS4Dot2) | `𝐒𝟒.𝟐`   |                 |
| $\mathbf{S4.3}$  | [LO.Modal.Normal.LogicS4Dot3](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicS4Dot3) | `𝐒𝟒.𝟑`   |                 |
| $\mathbf{S4Grz}$ | [LO.Modal.Normal.LogicS4Grz](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicS4Grz) | `𝐒𝟒𝐆𝐫𝐳`  |                 |
| $\mathbf{S5}$    | [LO.Modal.Normal.LogicS5](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicS5) | `𝐒𝟓`     | Alias of `𝐊𝐓𝟓`. |
| $\mathbf{GL}$    | [LO.Modal.Normal.LogicGL](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Logics.html#LO.Modal.Normal.LogicGL) | `𝐆𝐋`     |                 |

|                                   |                                            | Definition                                 |   Notation   |
| :-------------------------------: | ------------------------------------------ | :----------------------------------------- | :----------: |
|      $M, w \models \varphi$       | Satisfy                                    | [LO.Modal.Normal.Formula.Satisfies](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Semantics.html#LO.Modal.Normal.Formula.Satisfies) | `w ⊧ᴹˢ[M] φ` |
|        $M \models \varphi$        | Valid on model (Models)                    | [LO.Modal.Normal.Formula.Models](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Semantics.html#LO.Modal.Normal.Formula.Models) |  `⊧ᴹᵐ[M] φ`  |
|        $F \models \varphi$        | Valid on frame (Frames)                    | [LO.Modal.Normal.Formula.Frames](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Semantics.html#LO.Modal.Normal.Formula.Frames) |  `⊧ᴹᶠ[F] φ`  |
|    $\Gamma \models^F \varphi$     | Consequence on frame                       | [LO.Modal.Normal.Formula.FrameConsequence](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Semantics.html#LO.Modal.Normal.Formula.FrameConsequence) | `Γ ⊨ᴹᶠ[F] φ` |
| $\Gamma \vdash_{\Lambda} \varphi$ | Hilbert-style Deduction on logic $\Lambda$ | [LO.Modal.Normal.Deduction](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/HilbertStyle.html#LO.Modal.Normal.Deduction) | `Γ ⊢ᴹ(Λ) φ`  |

### Theorem

- [Soundness of Hilbert-style deduction](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.Logic.Hilbert.sounds)
  ```lean
  theorem LO.Modal.Normal.Logic.Hilbert.sounds
      {α : Type u} [Inhabited α]
      {β : Type u} [Inhabited β]
      (Λ : AxiomSet α)
      (f : Frame β) (hf : f ∈ (FrameClass β α Λ))
      {p : LO.Modal.Normal.Formula α}
      (h : ⊢ᴹ(Λ) p) :
      ⊧ᴹᶠ[f] p
  ```
  - [Consistency](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.Logic.Hilbert.consistency)
    ```lean
    theorem LO.Modal.Normal.Logic.Hilbert.consistency
        {α : Type u}
        {β : Type u}
        (Λ : AxiomSet α)
        (hf : ∃ f, f ∈ (FrameClass β α Λ)) :
        ⊬ᴹ(Λ)! ⊥
    ```
  -  **WIP:** Currently, these theorems was proved where only `Λ` is `𝐊`, `𝐊𝐃`, `𝐒𝟒`, `𝐒𝟓`.

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
- 菊池 誠 (編者), 数学における証明と真理 ─ 様相論理と数学基礎論

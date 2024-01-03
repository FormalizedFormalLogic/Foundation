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

### Normal Modal Logic

In this formalization, _(Modal) Logic_ means sets of formulae.

| Logic            | Definition                   | Notation | Remarks         |
| :--------------- | ---------------------------- | :------- | --------------- |
| $\mathbf{K}$     | `LO.Modal.Normal.LogicK`     | `𝐊`      |                 |
| $\mathbf{S4}$    | `LO.Modal.Normal.LogicS4`    | `𝐒𝟒`     | Alias of `𝐊𝐓𝟒`. |
| $\mathbf{S4.2}$  | `LO.Modal.Normal.LogicS4Grz` | `𝐒𝟒.𝟐`   |                 |
| $\mathbf{S4.3}$  | `LO.Modal.Normal.LogicS4Grz` | `𝐒𝟒.𝟑`   |                 |
| $\mathbf{S4Grz}$ | `LO.Modal.Normal.LogicS4Grz` | `𝐒𝟒𝐆𝐫𝐳`  |                 |
| $\mathbf{S5}$    | `LO.Modal.Normal.LogicS5`    | `𝐒𝟓`     | Alias of `𝐊𝐓𝟓`. |
| $\mathbf{GL}$    | `LO.Modal.Normal.LogicGL`    | `𝐆𝐋`     |                 |

|                                   |                                            | Definition                                 |   Notation   |
| :-------------------------------: | ------------------------------------------ | :----------------------------------------- | :----------: |
|      $M, w \models \varphi$       | Satisfy                                    | `LO.Modal.Normal.Formula.Satisfies`        | `w ⊧ᴹˢ[M] φ` |
|        $M \models \varphi$        | Valid on model (Models)                    | `LO.Modal.Normal.Formula.Models`           |  `⊧ᴹᵐ[M] φ`  |
|        $F \models \varphi$        | Valid on frame (Frames)                    | `LO.Modal.Normal.Formula.Frames`           |  `⊧ᴹᶠ[M] φ`  |
|    $\Gamma \models^F \varphi$     | Consequence on frame                       | `LO.Modal.Normal.Formula.FrameConsequence` | `Γ ⊨ᴹᶠ[M] φ` |
| $\Gamma \vdash_{\Lambda} \varphi$ | Hilbert-style Deduction on logic $\Lambda$ | `LO.Modal.Normal.Deduction`                | `Γ ⊢ᴹ(Λ) φ`  |

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
        T ⊬ LO.FirstOrder.Arith.FirstIncompleteness.undecidable T ∧
        T ⊬ ~LO.FirstOrder.Arith.FirstIncompleteness.undecidable T
    ```

### Normal Modal Logic

- [Soundness of Hilbert-style deduction for $\mathbf{K}$](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.LogicK.Hilbert.sounds)
  ```lean
  theorem LogicK.Hilbert.sounds (f : Frame β) : ⊢ᴹ(𝐊) p → ⊧ᴹᶠ[f] p
  ```
  - [Consistency](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.LogicK.Hilbert.consistency)
  ```lean
  theorem LogicK.Hilbert.consistency : ⊬ᴹ(𝐊)! ⊥
  ```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of Peano arithmetic
- 菊池 誠 (編者), 数学における証明と真理 ─ 様相論理と数学基礎論

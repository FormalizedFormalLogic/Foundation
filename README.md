# lean4-logic

Formalizing Logic in Lean4

## Documents

- [Book](https://iehality.github.io/lean4-logic/book): Summary of results. **TODO**
- [Full Documentation](https://iehality.github.io/lean4-logic/docs)

## Main Results

- [Classical Propositional Logic](#classical-propositional-logic)
  - [Definition](#definition)
  - [Theorem](#theorem)
- [First-Order Logic](https://iehality.github.io/lean4-logic/book/first_order/index.html): First-Order Logic and Arithmetic.
  - [Gödel's First Incompleteness](https://iehality.github.io/lean4-logic/book/first_order/goedel1.html)
- [Superintuitionistic Logic](https://iehality.github.io/lean4-logic/book/superntuitionistic/index.html): Intuitionistic propositional logic and some variants.
- [Standard Modal Logic](https://iehality.github.io/lean4-logic/book/standard_modal/index.html): Propositional logic extended modal operators $\Box$ and $\Diamond$.

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

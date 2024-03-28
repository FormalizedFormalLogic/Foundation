# lean4-logic
Formalizing Logic in Lean4

https://iehality.github.io/lean4-logic/

## Table of Contents

- [lean4-logic](#lean4-logic)
  - [Table of Contents](#table-of-contents)
  - [Usage](#usage)
  - [Structure](#structure)
  - [Classical Propositional Logic](#classical-propositional-logic)
    - [Definition](#definition)
    - [Theorem](#theorem)
  - [Intuitionistic Propositional Logic](#intuitionistic-propositional-logic)
    - [Definitions](#definitions)
    - [Kripkean Semantics](#kripkean-semantics)
      - [Defininitions](#defininitions)
      - [Theorems](#theorems)
  - [First-Order Logic](#first-order-logic)
    - [Definition](#definition-1)
    - [Theorem](#theorem-1)
  - [Normal Modal Logic](#normal-modal-logic)
    - [Definition](#definition-2)
    - [Theorem](#theorem-2)
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

## Intuitionistic Propositional Logic

### Definitions

|                                   |                                            | Definition                                 |   Notation   |
| :-------------------------------: | ------------------------------------------ | :----------------------------------------- | :----------: |
| $\Gamma \vdash \varphi$       | Deduction　 | LO.Propositional.Intuitionistic.Deduction | `Γ ⊢ᴵ p` |
| | Deductive (Exists deduction) | LO.Propositional.Intuitionistic.Deductive | `Γ ⊢ᴵ! p` |

### Kripkean Semantics

#### Defininitions

|                                   |                                            | Definition                                 |   Notation   |
| :-------------------------------: | ------------------------------------------ | :----------------------------------------- | :----------: |
| $w \Vdash^M \varphi$       | Satisfy on Kripkean Model $M$ and its world $w$　 | LO.Propositional.Intuitionistic.Formula.KripkeSatisfies | `w ⊩[M] p` |
| $M \vDash \varphi$        | Models                    | LO.Propositional.Intuitionistic.Formula.KripkeModels |  `M ⊧ p`  |
| $\Gamma \models \varphi$        | Conequences                    | LO.Propositional.Intuitionistic.Formula.KripkeConsequence |  `Γ ⊨ᴵ p`  |

#### Theorems
- [Soundness](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Soundness.html#LO.Propositional.Intuitionistic.Kripke.sounds)
  ```lean
  theorem Kripke.sounds {Γ : Theory β} {p : Formula β} : (Γ ⊢ᴵ! p) → (Γ ⊨ᴵ p)
  ```
- [Completeness](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Completeness.html#LO.Propositional.Intuitionistic.Kripke.completes)
  ```lean
  theorem Kripke.completes
    [DecidableEq β] [Encodable β]
    {Γ : Theory β} {p : Formula β} : (Γ ⊨ᴵ p) → (Γ ⊢ᴵ! p)
  ```
- [Disjunction Property](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Completeness.html#LO.Propositional.Intuitionistic.Deduction.disjunctive)
  ```lean
  theorem Deduction.disjunctive
    [DecidableEq β] [Encodable β]
    {p q : Formula β} : (∅ ⊢ᴵ! p ⋎ q) → (∅ ⊢ᴵ! p) ∨ (∅ ⊢ᴵ! q)
  ```

## First-Order Logic

$\mathbf{PA^-}$ is not to be included in $\mathbf{I\Sigma}_n$ or $\mathbf{PA}$ for simplicity in this formalization.

### Definition
|                                     |                                                | Definition                 | Notation |
| :----:                              | ----                                           | ----                       | :----:   |
| $(\rm Cut)\vdash_\mathrm{T} \Gamma$ | Derivation in Tait-Calculus + Cut              | [LO.FirstOrder.Derivation](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Calculus.html#LO.FirstOrder.Derivation) | `⊢¹ Γ`   |
| $M \models \sigma$                  | Tarski's truth definition condition            | [LO.FirstOrder.Models](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Semantics/Semantics.html#LO.FirstOrder.Models) | `M ⊧ₘ σ` |
| $\mathbf{Eq}$                       | Axiom of equality                              | [LO.FirstOrder.Theory.Eq](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Basic/Eq.html#LO.FirstOrder.Theory.Eq) | `𝐄𝐪` |
| $\mathbf{PA^-}$                     | Finitely axiomatized fragment of $\mathbf{PA}$ | [LO.FirstOrder.Arith.Theory.peanoMinus](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.peanoMinus) | `𝐏𝐀⁻` |
| $\mathbf{I}_\mathrm{open}$          | Induction of open formula                      | [LO.FirstOrder.Arith.Theory.iOpen](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.iOpen) | `𝐈open` |
| $\mathbf{I\Sigma}_n$                | Induction of $\Sigma_n$ formula                | [LO.FirstOrder.Arith.Theory.iSigma](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.iSigma) | `𝐈𝚺` |
| $\mathbf{PA}$                       | peano arithmetic                               | [LO.FirstOrder.Arith.Theory.peano](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Arith/Theory.html#LO.FirstOrder.Arith.Theory.peano) | `𝐏𝐀` |

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
      [𝐄𝐪 ≾ T]
      [𝐏𝐀⁻ ≾ T]
      [LO.FirstOrder.Arith.SigmaOneSound T]
      [LO.FirstOrder.Theory.Computable T] :
      ¬LO.System.Complete T
  ```
  - [undecidable sentence](https://iehality.github.io/lean4-logic/Logic/FirstOrder/Incompleteness/FirstIncompleteness.html#LO.FirstOrder.Arith.undecidable)
    ```lean
    theorem LO.FirstOrder.Arith.undecidable
        (T : LO.FirstOrder.Theory ℒₒᵣ)
        [DecidablePred T]
        [𝐄𝐪 ≾ T]
        [𝐏𝐀⁻ ≾ T]
        [LO.FirstOrder.Arith.SigmaOneSound T]
        [LO.FirstOrder.Theory.Computable T] :
        T ⊬ LO.FirstOrder.Arith.FirstIncompleteness.undecidable T ∧
        T ⊬ ~LO.FirstOrder.Arith.FirstIncompleteness.undecidable T
    ```

## Normal Modal Logic

### Definition

In this formalization, _(Modal) Logic_ means set of axioms.

| Logic            | Definition                    | Notation | Remarks         |
| :--------------: | ----------------------------- | :------- | --------------- |
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
| $\Gamma \vdash_{\Lambda} \varphi$ | Hilbert-style Deduction on logic $\Lambda$ | [LO.Modal.Normal.Deduction](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/HilbertStyle.html#LO.Modal.Normal.Deduction) | `Γ ⊢ᴹ[Λ] φ`  |

### Theorem

- [Soundness of Hilbert-style deduction](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.Logic.Hilbert.sounds) for `𝐊` extend `𝐓`, `𝐁`, `𝐃`, `𝟒`, `𝟓` Extensions (i.e. `𝐊𝐃`, `𝐒𝟒`, `𝐒𝟓`, etc.)
  ```lean
  theorem LO.Modal.Normal.Logic.Hilbert.sounds
      {α : Type u} [Inhabited α]
      {β : Type u} [Inhabited β]
      (Λ : AxiomSet α)
      (f : Frame β) (hf : f ∈ (FrameClass β α Λ))
      {p : LO.Modal.Normal.Formula α}
      (h : ⊢ᴹ[Λ] p) :
      ⊧ᴹᶠ[f] p
  ```
  - [Consistency](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/Soundness.html#LO.Modal.Normal.Logic.Hilbert.consistency)
    ```lean
    theorem LO.Modal.Normal.Logic.Hilbert.consistency
        {α : Type u}
        {β : Type u}
        (Λ : AxiomSet α)
        (hf : ∃ f, f ∈ (FrameClass β α Λ)) :
        ⊬ᴹ[Λ]! ⊥
    ```
  -  **WIP:** Currently, these theorems was proved where only `Λ` is `𝐊`, `𝐊𝐃`, `𝐒𝟒`, `𝐒𝟓`.
- Strong Completeness of Hilbert-style deduction for `𝐊` extend `𝐓`, `𝐁`, `𝐃`, `𝟒`, `𝟓` Extensions
  ```
  def Completeness
    {α β : Type u}
    (Λ : AxiomSet β)
    (𝔽 : FrameClass α)
    := ∀ (Γ : Theory β) (p : Formula β), (Γ ⊨ᴹ[𝔽] p) → (Γ ⊢ᴹ[Λ]! p)

  theorem LogicK.Hilbert.completes
    {β : Type u} [inst✝ : DecidableEq β] :
    Completeness
      (𝐊 : AxiomSet β)
      (𝔽((𝐊 : AxiomSet β)) : FrameClass (MaximalConsistentTheory (𝐊 : AxiomSet β)))
  ```
- [Gödel-McKensey-Tarski Theorem](https://iehality.github.io/lean4-logic/Logic/Modal/Normal/ModalCompanion.html#LO.Modal.Normal.companion_Int_S4)
  ```lean
  def GTranslation : Intuitionistic.Formula α → Formula α
  postfix:75 "ᵍ" => GTranslation

  theorem companion_Int_S4
    [DecidableEq α] [Encodable α] [Inhabited α]
    {p : Intuitionistic.Formula β} : (∅ ⊢! p) ↔ (∅ ⊢ᴹ[𝐒𝟒]! pᵍ)
  ```

## References
- J. Han, F. van Doorn, A formalization of forcing and the unprovability of the continuum hypothesis
- W. Pohlers, Proof Theory: The First Step into Impredicativity
- P. Hájek, P. Pudlák, Metamathematics of First-Order Arithmetic
- R. Kaye, Models of peano arithmetic
- 田中 一之, ゲーデルと20世紀の論理学
- 菊池 誠 (編者), 『数学における証明と真理 ─ 様相論理と数学基礎論』
- P. Blackburn, M. de Rijke, Y. Venema, "Modal Logic"
- Open Logic Project, ["The Open Logic Text"](https://builds.openlogicproject.org/)
- R. Hakli, S. Negri, "Does the deduction theorem fail for modal logic?"
- G. Boolos, "The Logic of Provability"
- Huayu Guo, Dongheng Chen, Bruno Bentzen, _"Verified completeness in Henkin-style for intuitionistic propositional logic"_
  - https://arxiv.org/abs/2310.01916
  - https://github.com/bbentzen/ipl

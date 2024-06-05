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
| $\Gamma \vdash \varphi$       | Deduction　 | LO.Propositional.Intuitionistic.Deduction | `Γ ⊢ⁱ p` |
| | Deductive (Exists deduction) | LO.Propositional.Intuitionistic.Deductive | `Γ ⊢ⁱ! p` |

### Kripkean Semantics

#### Defininitions

|                                   |                                            | Definition                                 |   Notation   |
| :-------------------------------: | ------------------------------------------ | :----------------------------------------- | :----------: |
| $w \Vdash^M \varphi$       | Satisfy on Kripkean Model $M$ and its world $w$　 | LO.Propositional.Intuitionistic.Formula.KripkeSatisfies | `w ⊩[M] p` |
| $M \vDash \varphi$        | Models                    | LO.Propositional.Intuitionistic.Formula.KripkeModels |  `M ⊧ p`  |
| $\Gamma \models \varphi$        | Conequences                    | LO.Propositional.Intuitionistic.Formula.KripkeConsequence |  `Γ ⊨ⁱ p`  |

#### Theorems
- [Soundness](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Soundness.html#LO.Propositional.Intuitionistic.Kripke.sounds)
  ```lean
  theorem Kripke.sounds {Γ : Theory β} {p : Formula β} : (Γ ⊢ⁱ! p) → (Γ ⊨ⁱ p)
  ```
- [Completeness](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Completeness.html#LO.Propositional.Intuitionistic.Kripke.completes)
  ```lean
  theorem Kripke.completes
    [DecidableEq β] [Encodable β]
    {Γ : Theory β} {p : Formula β} : (Γ ⊨ⁱ p) → (Γ ⊢ⁱ! p)
  ```
- [Disjunction Property](https://iehality.github.io/lean4-logic/Logic/Propositional/Intuitionistic/Kripke/Completeness.html#LO.Propositional.Intuitionistic.Deduction.disjunctive)
  ```lean
  theorem Deduction.disjunctive
    [DecidableEq β] [Encodable β]
    {p q : Formula β} : (∅ ⊢ⁱ! p ⋎ q) → (∅ ⊢ⁱ! p) ∨ (∅ ⊢ⁱ! q)
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

## Standard Modal Logic

Assigned to: [@SnO2WMaN](https://github.com/SnO2WMaN)

As a general term for various modal logics commonly known as $\bf K$, $\bf S4$, etc., we refer to the logic defined on a language that includes the modal operators $\Box$ (Box) and $\Diamond$ (Diamond), where $\Diamond$ is defined as the dual of $\Box$ (i.e., $\Diamond \varphi \equiv \lnot\Box\lnot \varphi$), as *Standard Modal Logic*[^remark_standard_modal_logic].

[^remark_standard_modal_logic]: This term is probably not usual. We introducing for convenience in naming and organizing within our formalization.

> [!NOTE]
> Be cautious similar notations for different concepts.
> We use $\TeX$ notation for concept that unrelated to our formalization, and code block \`\` for related our formalization.
> - $\sf K$ (\`\sf K`\) is axiom schema unrelated to formalization.
> - $\bf K$ (\`\bf K\`) is logic urelated to formalization.
> - `𝗞` (Mathematical Sans-Serif Bold) is `AxiomSet` in formalization.
> - `𝐊` (Mathematical Bold Capital) is `DeductionParameter` in formalization.

### Axioms

As an example, describe about axiom $\sf K$. Other axioms such as $\sf T$ and $\sf 4$ follow the same manner.

```lean
-- Axiom schema
abbrev System.Axioms.K (p q : F) := □(p ⟶ q) ⟶ □p ⟶ □q

abbrev Modal.Standard.AxiomSet (α : Type*) := Set (Modal.Standard.Formula α)

abbrev Modal.Standard.AxiomSet.K : AxiomSet α := { System.Axioms.K p q | (p) (q) }

notation "𝗞" => Modal.Standard.AxiomSet.K
```

### Deduction System

Our Hilbert-style deduction system for modal logic is designed to take parameters.
These parameters are as follows.

```lean
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
  nec : Bool
```

- `axiomSet` is set of formula (aximos), For example, `𝗞`, `𝗞 ∪ 𝗧 ∪ 𝟰`.
- `nec` is flag to contain necessitation rule.

The parameter is called _Normal_ if `axiomSet` includes `𝗞` and `nec` is `true`.

In this formalization, logics that we usually refer to as $\bf K$, $\bf S4$, etc. is characterized by deduction parameter.

### Kripke Semantics

### Geach Axioms

### Theorems

#### Soundness for Kripke Semantics

Let deduction system of `𝓓` has necessitation. If `𝓓 ⊢! p` then `p` is valid on every frame in `𝔽(Ax(𝓓))`.

```lean
instance {𝓓 : DeductionParameter α} [HasNec 𝓓] : Sound 𝓓 𝔽(Ax(𝓓))
```

#### Consistency of Deduction System via Kripke Semantics

From soundness theorem, if `𝔽(Ax(𝓓))` is nonempty, deduction system of `𝓓` is consistent (i.e. not every formula is provable in `𝓓`).

```lean
instance [FrameClass.IsNonempty 𝔽(Ax(L))] : System.Consistent L
```

It is immediately apparent, frameclass of `𝔽(Ax(𝐊))` is nonempty, thus `𝐊` is consistent.

```lean
instance : FrameClass.IsNonempty 𝔽(Ax(𝐊))

instance : System.Consistent 𝐊
```

Futhermore, if `𝓓` is Geach logic, then its frameclass is nonempty, thus it is consistent.

```lean
instance [𝓓.IsGeach] : FrameClass.IsNonempty 𝔽(Ax(𝓓))

instance [𝓓.IsGeach] : System.Consistent 𝓓
```

#### Completeness for Kripke Semantics

Proof of Kripke Completeness using the usual way with Canonical frames and models.

If every axioms in `Ax(𝓓)` is valid in Canonical frame of `𝓓`, `𝓓` is called _Canonical_.

```
class Canonical (𝓓 : DeductionParameter α) [Inhabited (MCT 𝓓)] where
  realize : (CanonicalFrame 𝓓) ⊧* Ax(𝓓)
```

If `𝓓` is canonical and consistent, then `𝓓` is complete for `𝔽(Ax(𝓓))`.

```
instance [System.Consistent 𝓓] [Canonical 𝓓] : Complete 𝓓 𝔽(Ax(𝓓))
```

Immediately apparent that `𝐊` is canonical and `𝐊` is consistent mentioned above, then `𝐊` is complete.

```
instance : Canonical 𝐊

instance : Complete 𝐊 𝔽(Ax(𝐊))
```

Futhermore, if `𝓓` is Geach logic, then `𝓓` is canonical, thus it is complete.

```lean
instance [𝓓.IsGeach] : Canonical 𝓓

instance [𝓓.IsGeach] : Complete 𝓓 𝔽(Ax(𝓓))
```

#### Strength between Modal Logics

It is immediately apparent that, when `𝓓₁​` and `𝓓₂` are same inference rule[^strength_between_modal_logics_1], the logical strength between `𝓓₁` and `𝓓₂` is determined by the subset of their axiom set.

[^strength_between_modal_logics_1]: It is permissible that `𝓓₂` has all inference rule of `𝓓₁​`.

```lean
lemma reducible_of_subset (hNec : L₁.nec ≤ L₂.nec) (hAx : Ax(L₁) ⊆ Ax(L₂)) : L₁ ≤ₛ L₂ := by

lemma reducible_K_KT : 𝐊 ≤ₛ 𝐊𝐓
```

However, even without the subset of axiomset, it is possible to analyze the strength of logic via Kripke semantics, specifically by analyzing the properties of frames defined by the axioms. For example, since seriality follows from reflexivity, $\bf KT$ is stronger than $\bf KD$ ($\sf K \cup D \not\sube K \cup T$).

```lean
lemma reducible_of_definability
  [Sound 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Complete 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Definability Ax(𝓓₁​) P₁] [Definability Ax(𝓓₂) P₂]
  (hs : ∀ {F : Frame}, P₂ F → P₁ F)
  : 𝓓₁​ ≤ₛ 𝓓₂

theorem reducible_KD_KT : 𝐊𝐃 ≤ₛ 𝐊𝐓
```

By same argument, the equivalence of provability between logics can be analyzed. $\bf S5$ is equivalent to $\bf KT4B$ ($\sf K \cup T \cup 5 \neq K \cup T \cup 4 \cup B$).

```lean
lemma equiv_of_iff_definability
  [Sound 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Sound 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Complete 𝓓₁​ 𝔽(Ax(𝓓₁​))] [Complete 𝓓₂ 𝔽(Ax(𝓓₂))]
  [Definability Ax(𝓓₁​) P₁] [Definability Ax(𝓓₂) P₂]
  (h : ∀ {F : Frame}, P₁ F ↔ P₂ F) : 𝓓₁​ =ₛ 𝓓₂

theorem equiv_S5_KT4B : 𝐒𝟓 =ₛ 𝐊𝐓𝟒𝐁
```

#### Modal Companion

Through a translation called _Gödel Translation_ from propositional logic formula to modal logic formula, intuitionistic logic $\bf Int$ can be embedded into $\bf S4$. (This theorem is known as _Gödel-McKensey-Tarski Theorem_.)

```lean
def GoedelTranslation : Superintuitionistic.Formula α → Formula α

postfix:75 "ᵍ" => GoedelTranslation

theorem provable_efq_iff_provable_S4
  {p : Superintuitionistic.Formula α}
  : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ
```

The generalized version of this relationship is called _Modal Companion_. $(\bf Int,S4)$ has modal companion.

```lean
class ModalCompanion (i𝓓 : Superintuitionistic.DeductionParameter α) (m𝓓 : Modal.Standard.DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, i𝓓 ⊢! p ↔ m𝓓 ⊢! pᵍ

instance : ModalCompanion 𝐈𝐧𝐭 𝐒𝟒
```

#### Undefinability of Frame Property

There is no axiom set that irreflexivity of frame defines. In other words, as long as the inference rule of `𝓓` is only necessitation, no matter what axiom sets of `𝓓` has, deduction system of `𝓓` cannot be represent irreflexive Kripke frame.

```
theorem Kripke.undefinability_irreflexive : ¬∃ (Ax : AxiomSet α), (∀ {F : Frame}, (Irreflexive F.Rel) ↔ F ⊧* Ax)
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

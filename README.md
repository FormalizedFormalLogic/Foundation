# Arithmetization

Formalization of Arithmetization of Metamathematics. This project depends on [lean4-logic](https://github.com/iehality/lean4-logic/tree/master).

https://iehality.github.io/Arithmetization/

## Table of Contents
- [Arithmetization](#arithmetization)
  - [Table of Contents](#table-of-contents)
  - [Usage](#usage)
  - [Structure](#structure)
  - [Definions](#definions)
  - [Theorems](#theorems)

## Usage
  Add following to `lakefile.lean`.
  ```lean
  require arithmetization from git "https://github.com/iehality/Arithmetization"
  ```

## Structure

- **Vorspiel**: Supplementary definitions and theorems for Mathlib
- **Definability**: Definability of relations and functions
- **Basic**: Basic theories such as $\mathbf{PA}^-$, $\mathbf{I}_\mathrm{open}$
- **IDeltaZero**: Theory $\mathbf{I\Delta_0}$
  - **Exponential**
- **OmegaOne**: Theory $\mathbf{I\Delta_0 + \Omega_1}$
- **ISigmaOne**: Theory $\mathbf{I\Sigma_1}$

## Definions

|                           | Definition                                 |   Notation   |
| ------------------------- | :----------------------------------------- | :----------: |
| $\mathbf{\Omega_1}$ axiom | [LO.FirstOrder.Arith.Theory.omega₁](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Basic.html#LO.FirstOrder.Arith.Theory.omega%E2%82%81) | `𝛀₁` |

## Theorems
- [Order induction](https://iehality.github.io/Arithmetization/Arithmetization/Basic/Ind.html#LO.FirstOrder.Arith.Model.order_induction_h)
  ```lean
  theorem LO.FirstOrder.Arith.Model.induction_h
      {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [LO.FirstOrder.ModelsTheory M 𝐏𝐀⁻]
      {L : LO.FirstOrder.Language} [LO.FirstOrder.Language.ORing L]
      [LO.FirstOrder.Structure L M] [LO.FirstOrder.Structure.ORing L M]
      (Γ : LO.Polarity) (s : ℕ)
      [LO.FirstOrder.ModelsTheory M (LO.FirstOrder.Arith.Theory.indScheme L (LO.FirstOrder.Arith.Hierarchy Γ s))]
      {P : M → Prop} (hP : LO.FirstOrder.Arith.Model.DefinablePred L Γ s P)
      (ind : ∀ (x : M), (∀ y < x, P y) → P x) (x : M) :
      P x
  ```

- [Least number principle](https://iehality.github.io/Arithmetization/Arithmetization/Basic/Ind.html#LO.FirstOrder.Arith.Model.least_number_h)
  ```lean
  theorem LO.FirstOrder.Arith.Model.least_number_h
      {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [LO.FirstOrder.ModelsTheory M 𝐏𝐀⁻]
      {L : LO.FirstOrder.Language} [LO.FirstOrder.Language.ORing L]
      [LO.FirstOrder.Structure L M] [LO.FirstOrder.Structure.ORing L M]
      [LO.FirstOrder.Structure.Monotone L M]
      (Γ : LO.Polarity) (s : ℕ)
      [LO.FirstOrder.ModelsTheory M (LO.FirstOrder.Arith.Theory.indScheme L (LO.FirstOrder.Arith.Hierarchy Γ s))]
      {P : M → Prop} (hP : LO.FirstOrder.Arith.Model.DefinablePred L Γ s P)
      {x : M} (h : P x) :
      ∃ (y : M), P y ∧ ∀ z < y, ¬P z
  ```

- [$\mathbf{I\Sigma_n} = \mathbf{I\Pi_n}$](https://iehality.github.io/Arithmetization/Arithmetization/Basic/Ind.html#LO.FirstOrder.Arith.Model.models_iSigma_iff_models_iPi)
  ```lean
  theorem LO.FirstOrder.Arith.Model.models_iSigma_iff_models_iPi
      {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] {ν : ℕ} :
      M ⊧ₘ* 𝐈𝚺ν ↔ M ⊧ₘ* 𝐈𝚷ν
  ```

- Exponential is definable in $\mathbf{I\Delta_0}$ by $\mathbf{\Delta_0}$ formula
  - [LO.FirstOrder.Arith.Model.Exp.defined](https://iehality.github.io/Arithmetization/Arithmetization/IDeltaZero/Exponential/Exp.html#LO.FirstOrder.Arith.Model.Exp.defined)
    ```lean
    theorem LO.FirstOrder.Arith.Model.Exp.defined
        {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M] [LO.FirstOrder.ModelsTheory M 𝐈𝚫₀] :
        Δ₀-Relation LO.FirstOrder.Arith.Model.Exp via LO.FirstOrder.Arith.Model.Exp.def
    ```

  - [Representation of $\mathbf{\Delta_0}$ definition of exponential](https://github.com/iehality/Arithmetization/blob/master/Arithmetization/IDeltaZero/Exponential/exp.pdf)
- Nuon (number of ones) is definable in $\mathbf{I\Delta_0 + \Omega_1}$ by $\mathbf{\Delta_0}$ formula
  - [LO.FirstOrder.Arith.Model.nuon_defined](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Nuon.html#LO.FirstOrder.Arith.Model.nuon_defined)
    ```lean
    theorem LO.FirstOrder.Arith.Model.nuon_defined
        {M : Type} [Zero M] [One M] [Add M] [Mul M] [LT M]
        [LO.FirstOrder.ModelsTheory M 𝐈𝚫₀] [LO.FirstOrder.ModelsTheory M 𝛀₁] :
        Δ₀-Function₁ LO.FirstOrder.Arith.Model.nuon via LO.FirstOrder.Arith.Model.nuonDef
    ```

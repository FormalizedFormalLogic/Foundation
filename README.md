# Arithmetization

Formalization of Arithmetization of Metamathematics.

https://iehality.github.io/Arithmetization/

## Table of Contents

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

- Exponential is definable in $\mathbf{I\Delta_0}$ by $\mathbf{\Delta_0}$ formula
  - [LO.FirstOrder.Arith.Model.Exp.defined](https://iehality.github.io/Arithmetization/Arithmetization/IDeltaZero/Exponential/Exp.html#LO.FirstOrder.Arith.Model.Exp.defined)
- Nuon (number of ones) is definable in $\mathbf{I\Delta_0 + \Omega_1}$ by $\mathbf{\Delta_0}$ formula
  - [LO.FirstOrder.Arith.Model.nuon_defined](https://iehality.github.io/Arithmetization/Arithmetization/OmegaOne/Nuon.html#LO.FirstOrder.Arith.Model.nuon_defined)
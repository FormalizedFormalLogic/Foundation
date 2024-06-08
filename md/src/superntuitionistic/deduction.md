# Deduction System

Our Hilbert-style deduction system for propositional logic is designed to take parameters.
These parameters are as follows.

```lean
structure DeductionParameter (α) where
  axiomSet : AxiomSet α
```

- `axiomSet` is set of formula (aximos), For example, `𝗘𝗙𝗤`, `𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠`.

In this formalization, logics that we usually refer to as $\bf Int$ (Intuitionistic Propositional Logic), $\bf Cl$ (Classical Propositional Logic), etc. is characterized by deduction parameter.

## Well-Known Systems

|Name | Notation | Axioms |
| :-   | :-: | -- |
| Minimal|       | `∅` |
| Intuitionistic | `𝐈𝐧𝐭` | `𝗘𝗙𝗤` |
| Classical| `𝐂𝐥`  | `𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠`  |

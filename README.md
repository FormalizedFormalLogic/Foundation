[Docs]: https://FormalizedFormalLogic.github.io/Foundation/docs
[Catalogue]: https://FormalizedFormalLogic.github.io/Catalogue
[Zoo]: https://github.com/FormalizedFormalLogic/Zoo
[ProvabilityLogic]: https://github.com/FormalizedFormalLogic/ProvabilityLogic
[FFL]: https://github.com/FormalizedFormalLogic

# Foundation

[![CI](https://github.com/FormalizedFormalLogic/Foundation/actions/workflows/ci.yml/badge.svg)](https://github.com/FormalizedFormalLogic/Foundation/actions/workflows/ci.yml)
[![License: Apache 2.0](https://img.shields.io/github/license/FormalizedFormalLogic/Foundation)](./LICENSE)

Formalizing mathematical logic in Lean 4.

This repository is the core library of [Formalized Formal Logic][FFL]: the syntax, proof systems, and semantics of propositional, first-order, and second-order logic, together with arithmetic, set theory, and the incompleteness theorems.
Results building on top of it (provability logic, modal logic, …) live in separate repositories, see [Further Results](#further-results).

## Structure & Summary

Main results of this repository. More detailed explanations are provided in the [Catalogue] and [Docs].

- `Logic`: Fundamental notions shared by all logics (entailment, semantics, calculi, Lindenbaum algebras, …).
- `Propositional`: Propositional logic (classical and intuitionistic).
  - [Completeness of Tait calculus][prop:completeness]
- `FirstOrder`: [First-order logic][first_order]
  - [Completeness theorem][first_order:completeness]
  - [Cut-elimination of first-order sequent calculus _(Gentzen's Hauptsatz)_][first_order:hauptsatz]
  - [Gödel–Gentzen negative translation][first_order:goedel_translation]
  - [Downward Löwenheim–Skolem theorem][first_order:downward_loewenheim_skolem]
  - [Intuitionistic first-order logic and Kripke semantics][first_order:intuitionistic]
  - [Arithmetic][arith]: arithmetical theories ($\mathsf{PA^-}$, $\mathsf{I}\Sigma_n$, $\mathsf{I\Delta_0 + \Omega_1}$, $\mathsf{R_0}$, $\mathsf{Q}$, …), definability, exponentiation, hereditarily finite sets, and true arithmetic.
    - [Arithmetic Theory Zoo](#arithmetic-theory-zoo)
  - [Bootstrapping][bootstrapping]: arithmetization of syntax and provability in $\mathsf{I}\Sigma_1$, the fixed-point theorem, and the Hilbert–Bernays–Löb derivability conditions.
  - [Incompleteness][incompleteness]
    - Gödel's [First][arith:goedel_it1] and [Second][arith:goedel_it2] incompleteness theorems
    - [Löb's theorem][arith:loeb]
    - [Tarski's undefinability of truth][arith:tarski]
    - [Church's theorem and undecidability of first-order logic][arith:church]
    - [Incompleteness via the halting problem][arith:halting]
    - [Rosser's][arith:rosser] and [restricted][arith:restricted] provability predicates
  - [Set theory][set_theory]: $\mathsf{Z}$, $\mathsf{ZF}$, $\mathsf{ZFC}$ and their models.
    - [Consistency of ZFC][set_theory:zfc_consistent] (relative to Lean's type theory)
    - [Downward Löwenheim–Skolem theorem for models of set theory][set_theory:loewenheim_skolem]
    - [Set Theory Zoo](#set-theory-zoo)
- `SecondOrder`: Syntax, semantics, and derivations of second-order logic.
- `Meta`: Proof automation.
- `Vorspiel`: Supplemental definitions and theorems for Mathlib.

[prop:completeness]: ./Foundation/Propositional/Boolean/Tait.lean
[first_order]: ./Foundation/FirstOrder
[first_order:completeness]: ./Foundation/FirstOrder/Completeness/CounterModel.lean
[first_order:hauptsatz]: ./Foundation/FirstOrder/Hauptsatz.lean
[first_order:goedel_translation]: ./Foundation/FirstOrder/NegationTranslation/GoedelGentzen.lean
[first_order:downward_loewenheim_skolem]: ./Foundation/FirstOrder/Skolemization/Hull.lean
[first_order:intuitionistic]: ./Foundation/FirstOrder/Intuitionistic
[arith]: ./Foundation/FirstOrder/Arithmetic
[bootstrapping]: ./Foundation/FirstOrder/Bootstrapping
[incompleteness]: ./Foundation/FirstOrder/Incompleteness
[arith:goedel_it1]: ./Foundation/FirstOrder/Incompleteness/First.lean
[arith:goedel_it2]: ./Foundation/FirstOrder/Incompleteness/Second.lean
[arith:loeb]: ./Foundation/FirstOrder/Incompleteness/Löb.lean
[arith:tarski]: ./Foundation/FirstOrder/Incompleteness/Tarski.lean
[arith:church]: ./Foundation/FirstOrder/Incompleteness/Church.lean
[arith:halting]: ./Foundation/FirstOrder/Incompleteness/Halting.lean
[arith:rosser]: ./Foundation/FirstOrder/Incompleteness/RosserProvability.lean
[arith:restricted]: ./Foundation/FirstOrder/Incompleteness/RestrictedProvability.lean
[set_theory]: ./Foundation/FirstOrder/SetTheory
[set_theory:zfc_consistent]: ./Foundation/FirstOrder/SetTheory/Universe.lean
[set_theory:loewenheim_skolem]: ./Foundation/FirstOrder/SetTheory/LoewenheimSkolem.lean

## Further Results

Results that depend on Foundation but are developed in their own repositories under the [Formalized Formal Logic][FFL] organization:

- [ProvabilityLogic]: provability logics ($\mathsf{GL}$ and its relatives), their Kripke semantics, and arithmetical completeness via the provability predicates formalized here.

See the [organization page][FFL] for the other repositories.

## Documents

- [Docs]: catalogue of definitions and theorems, _generated by [doc-gen4](https://github.com/leanprover/doc-gen4)_.
- [Catalogue]: an overview of the formalized results across the organization.

## Zoo

Automatically generated[^1] diagrams "Zoo" illustrate the Lean 4-verified interrelationships among theories and proof systems.

[^1]: To reduce build time in GitHub Actions, generated in a separate repository, see [Zoo].

- A solid arrow $\mathsf{A} \leftarrow \mathsf{B}$ indicates that $\mathsf{B}$ is strictly stronger than $\mathsf{A}$; that is, $\mathsf{B}$ is stronger than $\mathsf{A}$, while $\mathsf{A}$ is not stronger than $\mathsf{B}$, in terms of provability strength.
- A dashed arrow $\mathsf{A} \dashleftarrow \mathsf{B}$ indicates that $\mathsf{B}$ is stronger than $\mathsf{A}$ in terms of provability strength.
- A double line $\mathsf{A} \xlongequal{} \mathsf{B}$ indicates that $\mathsf{A}$ and $\mathsf{B}$ are equivalent in terms of provability strength.

### Arithmetic Theory Zoo

![Arithmetic Theory Zoo](https://formalizedformallogic.github.io/Zoo/arithmetic.png)

### Set Theory Zoo

![Set Theory Zoo](https://formalizedformallogic.github.io/Zoo/set_theory.png)

## Building

Foundation is a [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) project depending on [Mathlib](https://github.com/leanprover-community/mathlib4); the Lean version is pinned in [`lean-toolchain`](./lean-toolchain).

```shell
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

## Contributing

Contributions are welcome. Before opening a pull request, please read:

- [`CONTRIBUTING.md`](./CONTRIBUTING.md) — how changes land on `master`, PR/commit title conventions, pre-submission checks, and disclosure of AI involvement.
- [`contribute/style.md`](./contribute/style.md) — coding conventions for the Lean sources.
- [`contribute/refactoring.md`](./contribute/refactoring.md) — guidelines for refactoring existing proofs.

All changes go through pull requests and are squash-merged; the PR title becomes the commit message on `master`.
Whenever an AI coding agent was involved in producing a change, this must be disclosed as described in `CONTRIBUTING.md`.

## Developers

List of contact information and areas of expertise of the current main developers.
If you have any interest or questions, [create a new issue](https://github.com/FormalizedFormalLogic/Foundation/issues) or contact us directly.

- Palalansoukî (Shogo Saito, [@iehality][iehality:github], ✉️:[palalansouki@gmail.com][iehality:email])
  - Overall design and maintenance.
  - First-order logic.
  - Intuitionistic first-order logic.
  - Arithmetic, set theory, and incompleteness.
  - Proof automation.
  - Provability logic.
- SnO2WMaN (Mashu Noguchi, [@SnO2WMaN][sno2wman:github], ✉️:[me@sno2wman.net][sno2wman:email])
  - Modal logic.
  - Propositional logic (including intermediate logic).
  - Provability logic.
  - Interpretability logic.
  - Miscellaneous repository maintenance (e.g. GitHub Actions).

[iehality:github]: https://github.com/iehality
[iehality:email]: mailto:palalansouki@gmail.com
[sno2wman:github]: https://github.com/SnO2WMaN
[sno2wman:email]: mailto:me@sno2wman.net

## Citation

If you wish to cite this repository in academic papers, refer to [`CITATION.cff`](./CITATION.cff).

## License

This project is licensed under the [Apache License 2.0](./LICENSE).

## Financial Supports

Any financial support would be greatly appreciated.
If you find this project valuable, please consider supporting us to sustain our OSS development.

### Open Collective

[![Open Collective](https://opencollective.com/formalizedformallogic/donate/button.png?color=gray)][opencollective]

We would like to thank the following backers.

[![Open Collective Backers](https://opencollective.com/formalizedformallogic/backers.svg)][opencollective:backers]

[opencollective]: https://opencollective.com/formalizedformallogic
[opencollective:backers]: https://opencollective.com/formalizedformallogic#backers

### Previous Backers

Individuals and organizations that have supported us in the past.

- [Proxima Technology](https://proxima-ai-tech.com) (2024-2025)
- [随時 (@zuizi)](https://x.com/zuizi) (2025-10)

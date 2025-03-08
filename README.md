[Book]: https://formalizedformallogic.github.io/Foundation/book
[Doc]: https://FormalizedFormalLogic.github.io/Foundation/doc

# Foundation

Formalizing mathematical logics in Lean 4.

## Summary

Main Result in this repository. More results and details are in [Book] and [Doc].

- [Propositional Logic][prop]
  - [Tait-style calculus][prop:classical_tait] and [completeness][prop:classical_tait_complete]
  - [Completeness for Kripke semantics][prop:kripke]
  - [Disjunctive Property of intuitionistic logic][prop:int_disjunctive]
  - Rejection Law of Excluded Middle in intuitionistic logic and [sublogic relations][prop:sublogics]
- [First-Order Logic][first_order] and [Arithmetics][arith]
  - [Completeness Theorem][first_order:completeness]
  - [Gödel-Gentzen Translation][first_order:goedel_translation]
  - [Cut-elimination of first-order sequent calculus _(Gentzen's Hauptsatz)_][first_order:haupstaz]
  - [Arithmetic][arith] and [Arithmetization](arithmetization)
  - Gödel's [First][arith:goedel_it1] and [Second][arith:goedel_it2] Incompleteness Theorems
- [Basic Modal Logic][modal:logic] (with modal operators $\Box, \Diamond$)
  - [Kripke completeness for well-known subsystems][modal:logic_kripke_completeness]
  - [_Modal Cube_][modal:cube], and [sublogic relations for other logics](modal:sublogic)
  - [Gödel-McKinsey-Tarski Theorem][modal:gmt_theorem] and [Modal Companions](modal:companion)
  - [Provability Logic][provability_logic]

[prop]: ./Foundation/Propositional
[prop:classical_tait]: ./Foundation/Propositional/Tait/Calculus.lean
[prop:classical_tait_complete]: ./Foundation/Propositional/Classical/Tait.lean
[prop:classical_complete]: ./Foundation/Propositional/Classical/Tait.lean
[prop:kripke]: ./Foundation/Propositional/Kripke
[prop:int_disjunctive]: ./Foundation/Propositional/Kripke/Hilbert/Int.lean
[prop:sublogics]: ./Foundation/Propositional/Logic/Sublogic.lean
[first_order]: https://formalizedformallogic.github.io/Book/first_order/index.html
[first_order:completeness]: https://formalizedformallogic.github.io/Book/first_order/completeness.html
[first_order:haupstaz]: ./Foundation/FirstOrder/Hauptsatz.lean
[first_order:goedel_translation]: ./Foundation/IntFO/Translation.lean
[arith]: https://formalizedformallogic.github.io/Book/first_order/arithmetics.html
[arithmetization]: ./Foundation/Arithmetization
[arith:goedel_it1]: https://formalizedformallogic.github.io/Book/first_order/goedel1.html
[arith:goedel_it2]: https://formalizedformallogic.github.io/Book/first_order/goedel2.html
[modal:logic]: ./Foundation/Modal
[modal:logic_kripke_completeness]: ./Foundation/Modal/Kripke/Hilbert
[modal:cube]: ./Foundation/Modal/Logic/Sublogic/ModalCube.lean
[modal:sublogic]: ./Foundation/Modal/Logic/Sublogic
[modal:gmt_theorem]: ./Foundation/Modal/ModalCompanion/Int.lean
[modal:companion]: ./Foundation/Modal/ModalCompanion
[provability_logic]: ./Foundation/Incompleteness/ProvabilityLogic

## Documents

- [Book], summary of results.
- [Doc], documentation generated by [doc-gen4](https://github.com/leanprover/doc-gen4).

## Sponsor

This project is supported by [Proxima Technology].

[<img height="60" src="https://raw.githubusercontent.com/FormalizedFormalLogic/.github/refs/heads/main/profile/proxima_technology.svg">][Proxima Technology]

[Proxima Technology]: https://proxima-ai-tech.com/

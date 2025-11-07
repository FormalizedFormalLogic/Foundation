import Book.Init

open LO.Modal

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open LO
open Modal Neighborhood

set_option verso.docstring.allowMissing true

open LO

#doc (Manual) "Monthly Report 2025/10" =>
%%%
tag  := "monthly-report-2025-10"
%%%

This page is the monthly report summarizing commits [between 2025/10/01 and 2025/11/01](https://github.com/FormalizedFormalLogic/Foundation/commits/master/?since=2025-10-01&until=2025-11-01).
There are 4 major topics in this month.

# Set Theory and Consistency of `ZFC`

# Downward Löwenheim-Skolem Theorem

# Filteration of Neighborhood Semantics on Modal logic

_Author_: [@SnO2WMaN](https://github.com/SnO2WMaN)

Filtration in neighborhood semantics for modal logic has been studied
mainly for extensions of logic `E` by the axioms `M`, `C`, and `N`,
as well as for non-iterative axioms (i.e., those of modal depth at most 1)
by Lewis's Theorem ({citet Lew74}[]).
However, beyond these cases, very few results are known.

Recently, {citet Kop23}[] showed that logics containing
axiom `4` also enjoy the finite frame property (FFP) via filtration.
Since axiom `4` is not non-iterative,
Lewis’s theorem cannot be applied, and a nontrivial construction of the filtration is required.
However, Kopnev’s work exists only as an arXiv preprint and
does not have been reviewed and officially published.
During our verification, we found one missing case in the proof,
but the main argument remains correct once this gap is addressed.

In this project, we formalized Kopnev’s result.
In particular, formalized the FFP of logics `E4`, `ET4`, `EMC4` and `EMT4` via filtration.

{docstring E4.Neighborhood.finite_complete}

{docstring ET4.Neighborhood.finite_complete}

{docstring EMC4.Neighborhood.finite_complete}

{docstring EMT4.Neighborhood.finite_complete}

And as easy corollaries about and `N`, also formalized in FFP of `EN4`, `EMCN4`, `EMNT4`.

{docstring EN4.Neighborhood.finite_complete}

{docstring EMNT4.Neighborhood.finite_complete}

{docstring EMCN4.Neighborhood.finite_complete}

Remarks that `EMCN4` is equivalent to `K4`.

_Author note_: We noticed that forgot to formalize the FFP of `EMCNT4`, that is equivalent to `S4`, it might be proved easily.

More information might be found in {ref "modal-logic-neighborhood-semantics"}[chapter of neightborhood semantics on modal logic].
_(work in progress)_

# Interpretability Logic and Veltman Semantics

# Commits

- `3a9f118c`: add(FirstOrder): ZFC is consistent ([#606](https://github.com/FormalizedFormalLogic/Foundation/pull/606))
- `fee7c6e4`: add(FirstOrder): forcing part.1 ([#604](https://github.com/FormalizedFormalLogic/Foundation/pull/604))
- `fc53bbd3`: add(InterpretabilityLogic): Veltman semantics and soundness ([#602](https://github.com/FormalizedFormalLogic/Foundation/pull/602))
- `263961ed`: refactor(FirstOrder): structure ([#603](https://github.com/FormalizedFormalLogic/Foundation/pull/603))
- `b41e28ef`: refactor(FirstOrder): refactor arithmetic ([#573](https://github.com/FormalizedFormalLogic/Foundation/pull/573))
- `d97591fe`: add(FirstOrder): downward Löwenheim-Skolem theorem ([#599](https://github.com/FormalizedFormalLogic/Foundation/pull/599))
- `a5548d9a`: rename(FirstOrder): `Interpretation` ↦ `DirectInterpretation`  ([#598](https://github.com/FormalizedFormalLogic/Foundation/pull/598))
- `7285d2a1`: add(FirstOrder/SetTheory): cardinals in set theory, part 1 ([#579](https://github.com/FormalizedFormalLogic/Foundation/pull/579))
- `325cc7c4`: refactor(Logic): rename & refactor ([#597](https://github.com/FormalizedFormalLogic/Foundation/pull/597))
- `7c23fc78`: add(Modal): `EMC` equals to `EMCK` ([#596](https://github.com/FormalizedFormalLogic/Foundation/pull/596))
- `87bb48ca`: add(Modal/Neighborhood): Soundness of `EK` and `EMK` ([#595](https://github.com/FormalizedFormalLogic/Foundation/pull/595))
- `05e54f4f`: add(IntFO): Heyting valued model ([#593](https://github.com/FormalizedFormalLogic/Foundation/pull/593))
- `9096b38a`: feat(IntFO): redefine Kripke model of intuitionistic first-order logic ([#591](https://github.com/FormalizedFormalLogic/Foundation/pull/591))
- `9f6fbe29`: add(Modal): Add `EMK` and syntactical analysis ([#590](https://github.com/FormalizedFormalLogic/Foundation/pull/590))
- `8eae9b15`: refactor(Neighborhood): Canonicity ([#589](https://github.com/FormalizedFormalLogic/Foundation/pull/589))
- `3a9556d5`: add(Modal/Algebra): Definitions of Magari algebra ([#195](https://github.com/FormalizedFormalLogic/Foundation/pull/195))
- `8c9d11bf`: docs(Book): Neighborhood filtration ([#585](https://github.com/FormalizedFormalLogic/Foundation/pull/585))
- `1840b19b`: docs: Fix fonts ([#588](https://github.com/FormalizedFormalLogic/Foundation/pull/588))
- `580bb22e`: add(Book): on G1 and G2 ([#586](https://github.com/FormalizedFormalLogic/Foundation/pull/586))
- `1807efa0`: chore: Update to `v4.24.0-rc1` ([#582](https://github.com/FormalizedFormalLogic/Foundation/pull/582))
- `3c96ded4`: rename: `goedel`/`Goedel` ↦ `gödel`/ `Gödel` ([#583](https://github.com/FormalizedFormalLogic/Foundation/pull/583))
- `4615adcf`: add(Modal/Neighborhood): FFP of `EN4`, `ENT4`, `EMNT4`, `EMCN4` ([#584](https://github.com/FormalizedFormalLogic/Foundation/pull/584))
- `8ac14dcb`: docs: Book by Verso ([#399](https://github.com/FormalizedFormalLogic/Foundation/pull/399))
- `835896e4`: ci: Fix CI trigger ([#581](https://github.com/FormalizedFormalLogic/Foundation/pull/581))
- `201c5092`: add(Modal/Neighborhood): Add some observations ([#577](https://github.com/FormalizedFormalLogic/Foundation/pull/577))
- `dfe9cc43`: add(FirstOrder/SetTheory): functions in `𝗭` ([#578](https://github.com/FormalizedFormalLogic/Foundation/pull/578))
- `f1acb057`: add(FirstOrder): ordinals in Zermelo set theoey ([#575](https://github.com/FormalizedFormalLogic/Foundation/pull/575))
- `201dd59f`: refactor(Modal/Neighborhood): Refactor ([#576](https://github.com/FormalizedFormalLogic/Foundation/pull/576))

import Book.Init

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open LO

set_option verso.docstring.allowMissing true


#doc (Manual) "Monthly Report 2025/11" =>
%%%
tag  := "monthly-report-2025-11"
%%%

This page is the monthly report summarizing commits [between 2025/11/02 and 2025/11/30](https://github.com/FormalizedFormalLogic/Foundation/commits/master/?since=2025-11-02&until=2025-11-30).
There are 2 major topics in this month.

# Kripke Semantics of Classical First-Order Logic

*Author*: [Palalansoukî](https://github.com/iehality)

We formalized the Kripke semantics of classical first-order logic, a.k.a. weak forcing and proved its soundness theorem.
This semantics is used when we working on forcing arguments.

Kripke semantics of classical first-order logic is defined by
interpretting its negation translation as usual Kripke semantics of intuitionistic first-order logic.

{docstring FirstOrder.KripkeModel.weaklyForces₀_iff_forces}

This semantics satisfises monotonicity, genericity and soundness.

{docstring FirstOrder.KripkeModel.WeaklyForces₀.monotone}

{docstring FirstOrder.KripkeModel.WeaklyForces₀.generic_iff}

{docstring FirstOrder.KripkeModel.WeaklyForces₀.sound}

# Downward Löwenheim-Skolem Theorem

*Author*: [Palalansoukî](https://github.com/iehality)

We formalized the downward Löwenheim-Skolem theorem for countable languages.
This theorem states that all structure of countable language, with its subset $`s`,
has a minimal elementary substructure contains $`s`, namely a Skolem hull of $`s`.

{docstring FirstOrder.Structure.SkolemHull}

{docstring FirstOrder.Structure.SkolemHull.subset}

{docstring FirstOrder.Structure.SkolemHull.elementaryEquiv}

And if the subset is countable, then the cardinality of the Skolem hull is at most countable.

{docstring FirstOrder.Structure.SkolemHull.card_le_aleph0}

# Commits

- `939c95d0`: refactor(Propositional): Rename slash operation ([#652](https://github.com/FormalizedFormalLogic/Foundation/pull/652))
- `ae01fdbd`: add(Propositional): Corsi's Subintuitionistic Logics Part.1 ([#648](https://github.com/FormalizedFormalLogic/Foundation/pull/648))
- `eaec7d6b`: add(FirstOrder/SetTheory): transitive model ([#646](https://github.com/FormalizedFormalLogic/Foundation/pull/646))
- `b6086365`: feat(FirstOrder): downward Löwenheim-Skolem theorem ([#645](https://github.com/FormalizedFormalLogic/Foundation/pull/645))
- `cf2dd056`: fix: typo ([#643](https://github.com/FormalizedFormalLogic/Foundation/pull/643))
- `4e445871`: refactor(InterpretabilityLogic): Rename extensions of `IL` ([#642](https://github.com/FormalizedFormalLogic/Foundation/pull/642))
- `3b30775e`: ci: Remove concurrency restriction ([#644](https://github.com/FormalizedFormalLogic/Foundation/pull/644))
- `fde948a8`: add(InterpretabilityLogic/Veltman): `ILR ⪱ ILRW` ([#640](https://github.com/FormalizedFormalLogic/Foundation/pull/640))
- `e7360604`: ci: Revert removing `github.sha` from cache key ([#641](https://github.com/FormalizedFormalLogic/Foundation/pull/641))
- `ec113467`: ci: Remove `BRAINSia/free-disk-space` action ([#639](https://github.com/FormalizedFormalLogic/Foundation/pull/639))
- `419d43a9`: docs: Fix `FUNDING.yml` ([#638](https://github.com/FormalizedFormalLogic/Foundation/pull/638))
- `b2b0985d`: chore(deps): bump actions/upload-pages-artifact from 3 to 4 ([#637](https://github.com/FormalizedFormalLogic/Foundation/pull/637))
- `77d7bd94`: chore(deps): bump actions/checkout from 4 to 5 ([#636](https://github.com/FormalizedFormalLogic/Foundation/pull/636))
- `42104ce0`: docs: Update README.md for financial supports ([#635](https://github.com/FormalizedFormalLogic/Foundation/pull/635))
- `2f7e8463`: ci: Fix cache strategy ([#634](https://github.com/FormalizedFormalLogic/Foundation/pull/634))
- `6dffa9a5`: add(InterpretabilityLogic): Logic `ILRStar`  ([#629](https://github.com/FormalizedFormalLogic/Foundation/pull/629))
- `215d1666`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `M₀` ([#630](https://github.com/FormalizedFormalLogic/Foundation/pull/630))
- `f5b6c320`: ci: Fix caching problem ([#632](https://github.com/FormalizedFormalLogic/Foundation/pull/632))
- `11a14cee`: docs: Monthly Reports 2025/10 ([#621](https://github.com/FormalizedFormalLogic/Foundation/pull/621))
- `b8837832`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `R` ([#628](https://github.com/FormalizedFormalLogic/Foundation/pull/628))
- `b8745ddd`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `F` ([#627](https://github.com/FormalizedFormalLogic/Foundation/pull/627))
- `8ee1b7d9`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `W` ([#619](https://github.com/FormalizedFormalLogic/Foundation/pull/619))
- `faaeca41`: refactor(Prop): Move `HilbertStyle` to `Propositional/Entailment` ([#592](https://github.com/FormalizedFormalLogic/Foundation/pull/592))
- `584942ab`: chore: Update to `v4.25.0-rc2` ([#620](https://github.com/FormalizedFormalLogic/Foundation/pull/620))
- `f830b90e`: add(FirstOrder): soundness of Kripke semantics of classical logic ([#613](https://github.com/FormalizedFormalLogic/Foundation/pull/613))
- `c1fbcc23`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `P` ([#618](https://github.com/FormalizedFormalLogic/Foundation/pull/618))
- `c02e0caf`: add(InterpretabilityLogic/Veltman): Frame condition on axiom `M` ([#617](https://github.com/FormalizedFormalLogic/Foundation/pull/617))
- `75bf19f7`: add(InterpretabilityLogic/Veltman): Separate sublogics of `IL` Part.1 ([#616](https://github.com/FormalizedFormalLogic/Foundation/pull/616))
- `ab3dd9a2`: docs: Fix typo ([#615](https://github.com/FormalizedFormalLogic/Foundation/pull/615))
- `772dce9e`: docs: Update README for 2025/10 ([#614](https://github.com/FormalizedFormalLogic/Foundation/pull/614))
- `e50bb0ea`: add(InterpretabilityLogic): Syntactical analysis on Sublogics of `IL` ([#611](https://github.com/FormalizedFormalLogic/Foundation/pull/611))

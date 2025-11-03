import Book.Init

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open LO FirstOrder SetTheory

set_option verso.docstring.allowMissing true
set_option linter.tacticAnalysis false
#doc (Manual) "Set Theory" =>
%%%
tag := "setTheory"
%%%

In this formalization, we use same approach as formalizations for arithmetic theories.

The language of set theory $`\mathcal{L}_\mathrm{set}` is defined as a relationnal theory with two relational symbols $`\in` and $`=`,
denoted as {lean}`ℒₛₑₜ`.

{docstring LO.FirstOrder.Language.set}

# Axioms and Schemata of Set Theory

We define basic 7 axioms and 2 axiom schemata.

{docstring LO.FirstOrder.SetTheory.Axiom.empty}

{docstring LO.FirstOrder.SetTheory.Axiom.extentionality}

{docstring LO.FirstOrder.SetTheory.Axiom.pairing}

{docstring LO.FirstOrder.SetTheory.Axiom.union}

{docstring LO.FirstOrder.SetTheory.Axiom.power}

{docstring LO.FirstOrder.SetTheory.Axiom.infinity}

{docstring LO.FirstOrder.SetTheory.Axiom.foundation}

{docstring LO.FirstOrder.SetTheory.Axiom.separationSchema}

{docstring LO.FirstOrder.SetTheory.Axiom.replacementSchema}

The theory obtained by excluding replacement schema from the above axioms and axiom schemata
is called Zermelo set theory {lean}`𝗭`.

{docstring LO.FirstOrder.SetTheory.Zermelo}

The theory of all the above axioms and axiom schemata
is called Zermelo-Fraelkel set theory {lean}`𝗭𝗙`.

{docstring LO.FirstOrder.SetTheory.ZermeloFraenkel}

# Axiom of Choice

And the axiom of choice ({lean}`𝗔𝗖`).

{docstring LO.FirstOrder.SetTheory.Axiom.choice}

{docstring LO.FirstOrder.SetTheory.AxiomOfChoice}

By adding {lean}`𝗔𝗖` to the previously defined theories, the theories {lean}`𝗭𝗖` and {lean}`𝗭𝗙𝗖` are defined.

{docstring LO.FirstOrder.SetTheory.ZermeloChoice}

{docstring LO.FirstOrder.SetTheory.ZermeloFraenkelChoice}

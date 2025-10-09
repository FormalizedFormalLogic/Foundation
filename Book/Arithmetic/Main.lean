import Book.Init
import Book.Arithmetic.ISigma0
import Book.Arithmetic.ISigma1
import Book.Arithmetic.Goedel1
import Book.Arithmetic.Goedel2

open Verso.Genre
open Verso.Genre.Manual

set_option verso.docstring.allowMissing true
set_option linter.tacticAnalysis false
#doc (Manual) "Arithmetic" =>
%%%
tag := "arithmetics"
%%%

In this formalization, we prefer developing arithmetic _model theoretic_, i.e.
show $`T \models \sigma` instead of $`T \vdash \sigma` (They are equivalent thanks to the completeness theorem.).

This approach has several advantages:

1 In general, writing a formalized proof (in formalized system!) is very tedious.
    Meta-proofs, on the other hand, tend to be relatively concise.
2 Many definitions and proofs of logic and algebra in Mathlib can be used.
3 Metaprogramming can streamline the proof process (especially `definability`).
4 It is easy to extend predicates and functions.
    When adding predicates or functions, it is necessary to extend its language by _extension by definition_ in case of formalized proof,
    but not in model theoretic approach.

This procedure is done as follows.
Suppose we wish to prove that the totality of an exponential function can be proved in $`\mathsf{I}\Sigma_1`
First, the graph of the exponential function must be defined. This is achieved by the following two definitions.

1 Semantic definition.

{docstring LO.ISigma0.Exponential}

2 Syntactic definition that expresses the semantic definition.

{docstring LO.ISigma0.Exponential.defined}

Then prove the totality.

-- TODO: Exponential.total

Since `Exponential` and `Exponential.total` are defined in all the model of $`\mathsf{I}\Sigma_1`,
`𝐈𝚺₁ ⊢! ∀' ∃' exponentialDef` is obtained by the completeness theorem.
This was the result we wanted to achieve.

{include 0 Book.Arithmetic.ISigma0}

{include 0 Book.Arithmetic.ISigma1}

{include 0 Book.Arithmetic.Goedel1}

{include 0 Book.Arithmetic.Goedel2}

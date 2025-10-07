import Book.Init

open LO.Modal

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true

#doc (Manual) "Hilbert Systems of Modal Logic" =>
%%%
tag := "modal-logic-hilbert-systems"
%%%

# Soundness

{docstring LO.Modal.Kripke.instSound_of_validates_axioms}

# For {lean}`LO.Modal.K`

Recall {lean}`LO.Modal.K` is defined by Hilbert system {lean}`LO.Modal.Hilbert.Normal`.

{docstring LO.Modal.instCompleteLogicNatFormulaFrameClassKK}

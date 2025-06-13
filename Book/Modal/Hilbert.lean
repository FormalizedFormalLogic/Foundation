import VersoBlog
import VersoManual

import Foundation.Modal.Kripke.Logic.K

import Book.References

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

{docstring Hilbert.Kripke.instSound_of_validates_axioms}

# For {lean}`Logic.K`

Recall {lean}`Logic.K` is defined by Hilbert system {lean}`Hilbert.K`.

{docstring Hilbert.K.Kripke.complete}

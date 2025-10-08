import Book.Init

open LO.Modal

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true

open LO

#doc (Manual) "Kripke Semantics" =>
%%%
%%%

# Soundness

{docstring Modal.Kripke.instSound_of_validates_axioms}

# For {lean}`Modal.K`

{docstring Modal.K.Kripke.sound}

{docstring Modal.K.Kripke.complete}

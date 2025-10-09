import Book.Init

open LO.Modal

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option verso.docstring.allowMissing true

open LO
open Modal Neighborhood

#doc (Manual) "Neighborhood Semantics" =>
%%%
%%%

# Minimal Modal Logic


# Neighborhood Semantics

## Canonical Model

## Filtration

Filtration for transitive axioms `4` is proposed in {citet Kop23}[].

{docstring transitiveFiltration}

{docstring supplementedTransitiveFiltration}

{docstring quasiFilteringTransitiveFiltration}

# Logics

We summarize the soundness and completeness in neighborhood semantics for the several minimal modal logics.

## For {lean}`Modal.E`

{docstring FrameClass.E}

{docstring E.Neighborhood.sound}

{docstring E.Neighborhood.complete}

## For {lean}`Modal.E4`

{docstring FrameClass.E4}

{docstring E4.Neighborhood.sound}

{docstring E4.Neighborhood.complete}

By using {lean}`transitiveFiltration`, we can show that {lean}`Modal.E4` enjoys FFP.

{docstring E4.Neighborhood.finite_complete}

## For {lean}`Modal.ET4`

{docstring FrameClass.ET4}

{docstring ET4.Neighborhood.sound}

{docstring ET4.Neighborhood.complete}

By using {lean}`transitiveFiltration`, we can show that {lean}`Modal.ET4` enjoys FFP.

{docstring ET4.Neighborhood.finite_complete}

## For {lean}`Modal.EMT4`

{docstring FrameClass.EMT4}

{docstring EMT4.Neighborhood.sound}

{docstring EMT4.Neighborhood.complete}

By using {lean}`supplementedTransitiveFiltration`, we can show that {lean}`Modal.EMT4` enjoys FFP.

{docstring EMT4.Neighborhood.finite_complete}

## For {lean}`Modal.EMC4`

{docstring FrameClass.EMC4}

{docstring EMC4.Neighborhood.sound}

{docstring EMC4.Neighborhood.complete}

By using {lean}`quasiFilteringTransitiveFiltration`, we can show that {lean}`Modal.EMC4` enjoys FFP.

{docstring EMC4.Neighborhood.finite_complete}

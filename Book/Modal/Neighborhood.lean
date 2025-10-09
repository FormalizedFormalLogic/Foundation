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

# Canonical Model

# Filtration

Filtration for transitive axioms `4` is proposed in {citet Kop23}[]. For this purpose, we need basis filtration, {lean}`transitiveFiltration`.

{docstring transitiveFiltration}

As the name suggests, {lean}`transitiveFiltration` is transitive.

{docstring transitiveFiltration.isTransitive}

Reflexivity is preserved when original model is reflexive.

{docstring transitiveFiltration.isReflexive}

To show that Contains-unit property is preserved is not trivial, it needs that `□⊤` is in the filter.

{docstring transitiveFiltration.containsUnit}

We expand {lean}`transitiveFiltration` to suites for several logics. First one is for monotonicity, we add supplementation for {lean}`transitiveFiltration`.

{docstring supplementedTransitiveFiltration}

By supplementation, monotonicity is recovered.

{docstring supplementedTransitiveFiltration.isMonotonic}

Similarly, transitivity, reflexivity and contains-unit property is preserved.

{docstring supplementedTransitiveFiltration.isTransitive}

{docstring supplementedTransitiveFiltration.isReflexive}

{docstring supplementedTransitiveFiltration.containsUnit}

Second one is for regularity, we add quasi-filtering for {lean}`transitiveFiltration`.

{docstring quasiFilteringTransitiveFiltration}

By quasi-filtering, regularity is recovered.

{docstring quasiFilteringTransitiveFiltration.isRegular}

Similarly, Transitivity and reflexivity are preserved, and contains-unit property is preserved.

{docstring quasiFilteringTransitiveFiltration.isMonotonic}

{docstring quasiFilteringTransitiveFiltration.isTransitive}

{docstring quasiFilteringTransitiveFiltration.containsUnit}

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

## For {lean}`Modal.ENT4`

Similar to `Modal.ET4`.

{docstring FrameClass.ENT4}

{docstring ENT4.Neighborhood.sound}

{docstring ENT4.Neighborhood.complete}

{docstring ENT4.Neighborhood.finite_complete}

## For {lean}`Modal.EMT4`

{docstring FrameClass.EMT4}

{docstring EMT4.Neighborhood.sound}

{docstring EMT4.Neighborhood.complete}

By using {lean}`supplementedTransitiveFiltration`, we can show that {lean}`Modal.EMT4` enjoys FFP.

{docstring EMT4.Neighborhood.finite_complete}

## For {lean}`Modal.EMNT4`

Similar to `Modal.EMT4`.

{docstring FrameClass.EMNT4}

{docstring EMNT4.Neighborhood.sound}

{docstring EMNT4.Neighborhood.complete}

{docstring EMNT4.Neighborhood.finite_complete}

## For {lean}`Modal.EMC4`

{docstring FrameClass.EMC4}

{docstring EMC4.Neighborhood.sound}

{docstring EMC4.Neighborhood.complete}

By using {lean}`quasiFilteringTransitiveFiltration`, we can show that {lean}`Modal.EMC4` enjoys FFP.

{docstring EMC4.Neighborhood.finite_complete}

## For {lean}`Modal.EMCN4`

Similar to `Modal.EMC4`.

{docstring FrameClass.EMCN4}

{docstring EMCN4.Neighborhood.sound}

{docstring EMCN4.Neighborhood.complete}

{docstring EMCN4.Neighborhood.finite_complete}

## For {lean}`Modal.ED`

{docstring FrameClass.ED}

{docstring ED.Neighborhood.sound}

## For {lean}`Modal.E5`

{docstring FrameClass.E5}

{docstring E5.Neighborhood.sound}

{docstring E5.Neighborhood.complete}

## For {lean}`Modal.EM`

{docstring FrameClass.EM}

{docstring EM.Neighborhood.sound}

{docstring EM.Neighborhood.complete}

## For {lean}`Modal.ET`

{docstring FrameClass.ET}

{docstring ET.Neighborhood.sound}

{docstring ET.Neighborhood.complete}

## For {lean}`Modal.EN`

{docstring FrameClass.EN}

{docstring EN.Neighborhood.sound}

{docstring EN.Neighborhood.complete}

## For {lean}`Modal.EC`

{docstring FrameClass.EC}

{docstring EC.Neighborhood.sound}

{docstring EC.Neighborhood.complete}

## For {lean}`Modal.ECN`

{docstring FrameClass.ECN}

{docstring ECN.Neighborhood.sound}

{docstring ECN.Neighborhood.complete}

## For {lean}`Modal.EMN`

{docstring FrameClass.EMN}

{docstring EMN.Neighborhood.sound}

{docstring EMN.Neighborhood.complete}

## For {lean}`Modal.EMT`

{docstring FrameClass.EMT}

{docstring EMT.Neighborhood.sound}

{docstring EMT.Neighborhood.complete}

## For {lean}`Modal.EMC`

{docstring FrameClass.EMC}

{docstring EMC.Neighborhood.sound}

{docstring EMC.Neighborhood.complete}

## For {lean}`Modal.EMCN`

{docstring FrameClass.EMCN}

{docstring EMCN.Neighborhood.sound}

{docstring EMCN.Neighborhood.complete}

## For {lean}`Modal.EP`

{docstring FrameClass.EP}

{docstring EP.Neighborhood.sound}

## For {lean}`Modal.EN4`

{docstring FrameClass.EN4}

{docstring EN4.Neighborhood.sound}

{docstring EN4.Neighborhood.complete}

## For {lean}`Modal.END`

{docstring FrameClass.END}

{docstring END.Neighborhood.sound}

## For {lean}`Modal.END4`

{docstring FrameClass.END4}

{docstring END4.Neighborhood.sound}

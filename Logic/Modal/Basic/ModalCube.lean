/-
 Reserved to ompare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Basic.HilbertStyle

namespace LO.Modal.Hilbert

open HasAxiomT HasAxiomD HasAxiomB HasAxiom4 HasAxiom5

section S5Equivalence

variable (F : Type u) [ModalLogicSymbol F] [System F] [Hilbert.Classical F] [HasNecessitation F] [HasAxiomK F] [LogicK F]
variable [HasAxiomT F] [HasAxiomD F] [HasAxiomB F] [HasAxiom4 F] [HasAxiom5 F]

private abbrev LogicKT5 := LogicS5

class LogicKTB5 [LogicK F] [HasAxiomT F] [HasAxiomB F] [HasAxiom5 F]

instance [LogicKTB5 F] : LogicKT5 F where

class LogicKT45 [LogicK F] [HasAxiomT F] [HasAxiom4 F] [HasAxiom5 F]

instance [LogicKT45 F] : LogicKT5 F where

class LogicKT4B [LogicK F] [HasAxiomT F] [HasAxiom4 F] [HasAxiomB F]

class LogicKT4B5 [LogicK F] [HasAxiomT F] [HasAxiom4 F] [HasAxiomB F] [HasAxiom5 F]

instance [LogicKT4B5 F] : LogicKT4B F where

instance [LogicKT4B5 F] : LogicKT5 F where

class LogicKDB5 [LogicK F] [HasAxiomD F] [HasAxiomB F] [HasAxiom5 F]

class LogicKD4B [LogicK F] [HasAxiomD F] [HasAxiom4 F] [HasAxiomB F]

class LogicKD4B5 [LogicK F] [HasAxiomD F] [HasAxiom4 F] [HasAxiomB F] [HasAxiom5 F]

instance [LogicKD4B5 F] : LogicKD4B F where

end S5Equivalence

end LO.Modal.Hilbert

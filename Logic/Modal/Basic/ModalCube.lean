/-
 Reserved to ompare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Basic.HilbertStyle

namespace LO.Modal.Hilbert

open HasAxiomT HasAxiomD HasAxiomB HasAxiom4 HasAxiom5

variable {Bew : Type u} [ModalLogicSymbol Bew] (Bew : Set Bew → Bew → Sort*)

section S5Equivalence

private abbrev LogicKT5 := LogicS5 Bew

class LogicKTB5 extends LogicK Bew, HasAxiomT Bew, HasAxiomB Bew, HasAxiom5 Bew

instance [LogicKTB5 Bew] : LogicKT5 Bew where

class LogicKT45 extends LogicK Bew, HasAxiomT Bew, HasAxiom4 Bew, HasAxiom5 Bew

instance [LogicKT45 Bew] : LogicKT5 Bew where

class LogicKT4B extends LogicK Bew, HasAxiomT Bew, HasAxiom4 Bew, HasAxiomB Bew

class LogicKT4B5 extends LogicK Bew, HasAxiomT Bew, HasAxiom4 Bew, HasAxiomB Bew, HasAxiom5 Bew

instance [LogicKT4B5 Bew] : LogicKT4B Bew where

instance [LogicKT4B5 Bew] : LogicKT5 Bew where

class LogicKDB5 extends LogicK Bew, HasAxiomD Bew, HasAxiomB Bew, HasAxiom5 Bew

class LogicKD4B extends LogicK Bew, HasAxiomD Bew, HasAxiom4 Bew, HasAxiomB Bew

class LogicKD4B5 extends LogicK Bew, HasAxiomD Bew, HasAxiom4 Bew, HasAxiomB Bew, HasAxiom5 Bew

instance [LogicKD4B5 Bew] : LogicKD4B Bew where

end S5Equivalence

end LO.Modal.Hilbert

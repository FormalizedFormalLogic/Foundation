/-
 Reserved to ompare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Basic.HilbertStyle

namespace LO.Modal.Hilbert

section S5Equivalence

variable (F : Type u) [ModalLogicSymbol F] [TwoSided F]

class LogicKTB5 extends LogicK F, HasAxiomT F, HasAxiom5 F

class LogicKT45 extends LogicK F, HasAxiomT F, HasAxiom4 F, HasAxiom5 F

class LogicKT4B5 extends LogicK F, HasAxiomT F, HasAxiom4 F, HasAxiomB F, HasAxiom5 F

class LogicKDB5 extends LogicK F, HasAxiomD F, HasAxiomB F, HasAxiom5 F

class LogicKD4B5 extends LogicK F, HasAxiomD F, HasAxiom4 F, HasAxiomB F, HasAxiom5 F

class LogicKT4B extends LogicK F, HasAxiomT F, HasAxiom4 F, HasAxiomB F

class LogicKD4B extends LogicK F, HasAxiomD F, HasAxiom4 F, HasAxiomB F

end S5Equivalence

end LO.Modal.Hilbert

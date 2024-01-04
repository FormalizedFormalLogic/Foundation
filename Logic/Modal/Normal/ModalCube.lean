/-
 Reserved to compare the strengh of normal modal logic proof systems.

 ## References

 * <https://plato.stanford.edu/entries/logic-modal/#MapRelBetModLog>
-/

import Logic.Modal.Normal.HilbertStyle

namespace LO.Modal.Normal

open Hilbert

variable {F : Type u} [ModalLogicSymbol F] (Bew : Set F → F → Sort*)

section LogicS5

instance [LogicS5.Hilbert Bew] : HasAxiomD Bew where
  D _ _ := by sorry;

instance [LogicS5.Hilbert Bew] : HasAxiomB Bew where
  B _ p := by sorry;

instance [LogicS5.Hilbert Bew] : HasAxiom4 Bew where
  A4 _ _ := by sorry;

/-- `𝐒𝟓` Without `𝐓` -/
class LogicKDB5.Hilbert extends LogicK.Hilbert Bew, HasAxiomD Bew, HasAxiomB Bew, HasAxiom5 Bew

instance [LogicKDB5.Hilbert Bew] : HasAxiom4 Bew where
  A4 _ _ := by sorry;

instance [LogicKDB5.Hilbert Bew] : LogicS5.Hilbert Bew where
  K _ p q := by sorry;
  T _ p := by sorry;
  A5 _ p := by sorry;

instance [LogicS5.Hilbert Bew] : LogicKDB5.Hilbert Bew where

/-- `𝐒𝟓` Without `𝟓` -/
class LogicKT4B.Hilbert extends LogicK.Hilbert Bew, HasAxiomT Bew, HasAxiom4 Bew, HasAxiomB Bew

instance [LogicKT4B.Hilbert Bew] : LogicS5.Hilbert Bew where
  K _ _ := by sorry;
  T _ _ := by sorry;
  A5 _ _ := by sorry;

instance [LogicS5.Hilbert Bew] : LogicKT4B.Hilbert Bew where

-- Without `𝐓` and `𝟓`
class LogicKD4B.Hilbert extends LogicK.Hilbert Bew, HasAxiomD Bew, HasAxiom4 Bew, HasAxiomB Bew

instance [LogicKD4B.Hilbert Bew] : LogicS5.Hilbert Bew where
  K _ _ := by sorry;
  T _ _ := by sorry;
  A5 _ _ := by sorry;

instance [LogicS5.Hilbert Bew] : LogicKD4B.Hilbert Bew where

end LogicS5

end LO.Modal.Normal

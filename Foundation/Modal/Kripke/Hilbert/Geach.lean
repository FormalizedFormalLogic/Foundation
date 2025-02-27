import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Hilbert.Geach
import Foundation.Modal.Kripke.Hilbert.Soundness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

instance MultiGeacheanFrameClass.isDefinedByGeachHilbertAxioms (ts)
  : (MultiGeacheanConfluentFrameClass ts).DefinedBy (Hilbert.Geach ts).axioms :=
  FrameClass.definedBy_with_axiomK (MultiGeacheanFrameClass.isDefinedByGeachAxioms ts)

end Kripke



namespace Hilbert.Geach

open Kripke

instance Kripke.sound : Sound (Hilbert.Geach G) (MultiGeacheanConfluentFrameClass G) := inferInstance

instance Kripke.Consistent : Entailment.Consistent (Hilbert.Geach G) := Kripke.Hilbert.consistent_of_FrameClass (Kripke.MultiGeacheanConfluentFrameClass G)

end Hilbert.Geach


end LO.Modal

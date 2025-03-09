import Foundation.Modal.Hilbert.Geach
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Soundness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

instance FrameClass.multiGeachean.definability' (G)
  : (FrameClass.multiGeachean G).DefinedBy (Hilbert.Geach G).axioms :=
  FrameClass.definedBy_with_axiomK (FrameClass.multiGeachean.definability G)

end Kripke



namespace Hilbert.Geach

open Kripke
open Kripke.Hilbert

instance Kripke.sound : Sound (Hilbert.Geach G) (FrameClass.multiGeachean G) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.Geach G) := consistent_of_FrameClass (FrameClass.multiGeachean G) (by simp)

end Hilbert.Geach


end LO.Modal

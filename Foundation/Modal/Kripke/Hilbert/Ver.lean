import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke

namespace Hilbert.Ver

instance Kripke.sound : Sound (Hilbert.Ver) FrameClass.isolated := by
  have := FrameClass.definedBy_with_axiomK FrameClass.isolated.definability;
  infer_instance;

instance Kripke.consistent : Entailment.Consistent (Hilbert.Ver) :=
  have := FrameClass.definedBy_with_axiomK FrameClass.isolated.definability;
  Kripke.Hilbert.consistent_of_FrameClass FrameClass.isolated

instance Kripke.complete : Complete (Hilbert.Ver) FrameClass.isolated := inferInstance

end Hilbert.Ver

end LO.Modal

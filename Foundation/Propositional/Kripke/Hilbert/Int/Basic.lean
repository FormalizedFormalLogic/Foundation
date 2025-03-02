import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Formula.Kripke

open Kripke

namespace Hilbert.Int.Kripke

instance sound : Sound Hilbert.Int AllFrameClass := inferInstance

instance consistent : Entailment.Consistent Hilbert.Int := Kripke.Hilbert.consistent_of_FrameClass AllFrameClass

instance canonical : Canonical Hilbert.Int AllFrameClass := by tauto;

instance complete: Complete Hilbert.Int AllFrameClass := inferInstance

end Hilbert.Int.Kripke


end LO.Propositional

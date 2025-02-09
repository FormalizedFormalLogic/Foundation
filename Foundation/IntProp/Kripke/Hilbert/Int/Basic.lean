import Foundation.IntProp.Hilbert.WellKnown
import Foundation.IntProp.Kripke.Completeness
import Foundation.IntProp.Kripke.Hilbert.Soundness

namespace LO.IntProp

open Formula.Kripke

open Kripke

namespace Hilbert.Int.Kripke

instance sound : Sound Hilbert.Int AllFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.Int := Kripke.Hilbert.consistent_of_FrameClass AllFrameClass

instance canonical : Canonical Hilbert.Int AllFrameClass := by tauto;

instance complete: Complete Hilbert.Int AllFrameClass := inferInstance

end Hilbert.Int.Kripke


end LO.IntProp

import Foundation.Modal.Kripke.Hilbert.Geach
import Foundation.Modal.Kripke.AxiomDot3

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveConnectedFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

namespace Hilbert.S4Dot3

end Hilbert.S4Dot3

end LO.Modal

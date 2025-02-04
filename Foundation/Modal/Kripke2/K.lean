import Foundation.Modal.Hilbert2.K
import Foundation.Modal.Kripke2.Soundness
import Foundation.Modal.Kripke2.Completeness

namespace LO.Modal

namespace Hilbert.K

instance : System.Consistent (Hilbert.K) := Kripke.Hilbert.instConsistent Kripke.AllFrameClass

instance : Complete (Hilbert.K) (Kripke.AllFrameClass) := Kripke.instCompleteOfCanonical trivial

end Hilbert.K

end LO.Modal

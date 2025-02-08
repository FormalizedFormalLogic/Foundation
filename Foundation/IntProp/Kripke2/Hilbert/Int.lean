import Foundation.IntProp.Hilbert2.Int
import Foundation.IntProp.Kripke2.Hilbert.Soundness

namespace LO.IntProp

open Formula.Kripke

open Kripke

namespace Hilbert.Int.Kripke

instance sound : Sound Hilbert.Int AllFrameClass := inferInstance

instance consistent : System.Consistent Hilbert.Int := Kripke.Hilbert.consistent_of_FrameClass AllFrameClass

end Hilbert.Int.Kripke


end LO.IntProp

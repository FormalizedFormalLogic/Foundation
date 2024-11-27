import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.Grz

namespace LO.Modal.Hilbert

open System
open Formula (atom)

lemma KT_weakerThan_S4 : (Hilbert.KT α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

end LO.Modal.Hilbert

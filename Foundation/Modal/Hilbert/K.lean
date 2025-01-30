import Foundation.Modal.Hilbert.Basic
import Foundation.Modal.System.Basic
import Foundation.Modal.Logic.Basic

namespace LO.Modal

namespace Hilbert

protected abbrev K (α) : Hilbert α := ⟨𝗞, ⟮Nec⟯⟩
instance : (Hilbert.K α).IsNormal where

end Hilbert


abbrev Logic.K (α) : Logic α := { φ | (Hilbert.K α) ⊢! φ }

end LO.Modal

import Foundation.Modal.Kripke2.AxiomVer
import Foundation.Modal.Kripke2.Soundness
import Foundation.Modal.Hilbert2.WellKnown

namespace LO.Modal

open Kripke

namespace Kripke

open System

variable {S} [System (Formula ℕ) S]
variable {𝓢 : S} [System.Consistent 𝓢]

instance [System.Ver 𝓢] : Canonical 𝓢 IsolatedFrameClass := ⟨by
  intro x y Rxy;
  have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
  exact this x _ Rxy;
⟩

end Kripke


namespace Hilbert.Ver

instance Kripke.Consistent : System.Consistent (Hilbert.Ver) :=
  haveI := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer
  Kripke.Hilbert.instConsistent IsolatedFrameClass

instance Kripke.Complete : Complete (Hilbert.Ver) IsolatedFrameClass := inferInstance

end Hilbert.Ver

end LO.Modal

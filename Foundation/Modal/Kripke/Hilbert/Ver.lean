import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke

namespace Kripke

open Entailment

variable {S} [Entailment (Formula ℕ) S]
variable {𝓢 : S} [Entailment.Consistent 𝓢]

instance [Entailment.Ver 𝓢] : Canonical 𝓢 IsolatedFrameClass := ⟨by
  intro x y Rxy;
  have : (canonicalModel 𝓢) ⊧ □⊥ := iff_valid_on_canonicalModel_deducible.mpr axiomVer!
  exact this x _ Rxy;
⟩

end Kripke


namespace Hilbert.Ver

instance Kripke.sound : Sound (Hilbert.Ver) IsolatedFrameClass := by
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  infer_instance;

instance Kripke.consistent : Entailment.Consistent (Hilbert.Ver) :=
  have := FrameClass.definedBy_with_axiomK IsolatedFrameClass.DefinedByAxiomVer;
  Kripke.Hilbert.consistent_of_FrameClass IsolatedFrameClass

instance Kripke.complete : Complete (Hilbert.Ver) IsolatedFrameClass := inferInstance

end Hilbert.Ver

end LO.Modal

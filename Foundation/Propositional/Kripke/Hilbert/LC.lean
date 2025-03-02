import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Kripke.AxiomDummett

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Hilbert.LC.Kripke

instance : ConnectedFrameClass.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.LC ConnectedFrameClass := inferInstance

instance consistent : Entailment.Consistent Hilbert.LC := Kripke.Hilbert.consistent_of_FrameClass ConnectedFrameClass

instance canonical : Canonical Hilbert.LC ConnectedFrameClass := ⟨Canonical.connected⟩

instance complete : Complete Hilbert.LC ConnectedFrameClass := inferInstance

end Hilbert.LC.Kripke


end LO.Propositional

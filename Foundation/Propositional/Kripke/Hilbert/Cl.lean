import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.AxiomLEM

namespace LO.Propositional

open Kripke
open Formula.Kripke

open Kripke

namespace Hilbert.Cl.Kripke

instance : FrameClass.euclidean.DefinedBy (Hilbert.Cl.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.Cl FrameClass.euclidean := inferInstance

instance consistent : Entailment.Consistent Hilbert.Cl := Kripke.Hilbert.consistent_of_FrameClass FrameClass.euclidean (by simp)

instance canonical : Canonical Hilbert.Cl FrameClass.euclidean := ⟨Canonical.euclidean⟩

instance complete : Complete Hilbert.Cl FrameClass.euclidean := inferInstance

end Hilbert.Cl.Kripke


end LO.Propositional

import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration

namespace LO.Propositional

open Kripke
open Formula.Kripke

instance : FrameClass.connected.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

protected abbrev Kripke.FiniteFrameClass.connected : FiniteFrameClass := { F | Connected F.Rel }

namespace Hilbert.LC.Kripke

instance : FrameClass.connected.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.LC FrameClass.connected := inferInstance

instance consistent : Entailment.Consistent Hilbert.LC := Kripke.Hilbert.consistent_of_FrameClass FrameClass.connected (by simp)

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨Canonical.connected⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

section FFP

instance sound_finite : Sound Hilbert.LC Kripke.FiniteFrameClass.connected := ⟨by
  intro φ hφ F hF;
  apply Hilbert.finite_sound_of_sound sound |>.sound hφ;
  simpa;
⟩

instance complete_finite : Complete (Hilbert.LC) Kripke.FiniteFrameClass.connected := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  intro F _ V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M ↑φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf) (by simp) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hφ;
  . sorry;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end FFP

end Hilbert.LC.Kripke

end LO.Propositional

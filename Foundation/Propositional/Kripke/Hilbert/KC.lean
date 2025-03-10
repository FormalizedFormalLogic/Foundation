import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration

namespace LO.Propositional

open Kripke
open Formula.Kripke

instance : FrameClass.confluent.DefinedBy (Hilbert.KC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

protected abbrev Kripke.FiniteFrameClass.confluent : FiniteFrameClass := { F | Confluent F.Rel }

namespace Hilbert.KC.Kripke

instance sound : Sound Hilbert.KC FrameClass.confluent := inferInstance

instance consistent : Entailment.Consistent Hilbert.KC := Kripke.Hilbert.consistent_of_FrameClass FrameClass.confluent (by simp)

instance canonical : Canonical Hilbert.KC FrameClass.confluent := ⟨Canonical.confluent⟩

instance complete : Complete Hilbert.KC FrameClass.confluent := inferInstance

section FFP

instance sound_finite : Sound Hilbert.KC Kripke.FiniteFrameClass.confluent := ⟨by
  intro φ hφ F hF;
  apply Hilbert.finite_sound_of_sound sound |>.sound hφ;
  simpa;
⟩

instance complete_finite : Complete (Hilbert.KC) Kripke.FiniteFrameClass.confluent := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F hF V x;
  let M : Kripke.Model := ⟨F, V⟩;
  let FM := finestFilterationTransitiveClosureModel M ↑φ.subformulas;
  apply filteration FM (finestFilterationTransitiveClosureModel.filterOf) (by simp) |>.mpr;
  apply validOnModel_of_validOnFiniteFrameClass hφ;
  . sorry;
  . apply FilterEqvQuotient.finite;
    simp;
⟩

end FFP

end Hilbert.KC.Kripke

end LO.Propositional

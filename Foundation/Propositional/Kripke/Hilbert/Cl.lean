import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.AxiomLEM

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev euclidean : FrameClass := { F | IsEuclidean _ F }

end Kripke.FrameClass


namespace Hilbert.Cl.Kripke

instance sound : Sound Hilbert.Cl FrameClass.euclidean :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_LEM_of_euclidean;

instance consistent : Entailment.Consistent Hilbert.Cl := consistent_of_sound_frameclass FrameClass.euclidean $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.Cl FrameClass.euclidean :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.Cl FrameClass.euclidean := inferInstance

end Hilbert.Cl.Kripke


end LO.Propositional

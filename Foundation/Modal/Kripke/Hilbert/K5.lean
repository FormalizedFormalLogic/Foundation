import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.eucl : FrameClass := { F | IsEuclidean _ F }

namespace Hilbert.K5.Kripke

instance sound : Sound (Hilbert.K5) Kripke.FrameClass.eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_eucl _ rfl;
  exact validate_AxiomFive_of_euclidean (eucl := F_eucl);

instance consistent : Entailment.Consistent (Hilbert.K5) := consistent_of_sound_frameclass FrameClass.eucl $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.K5) Kripke.FrameClass.eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.K5) Kripke.FrameClass.eucl := inferInstance

end Hilbert.K5.Kripke

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.corefl : FrameClass := { F | IsCoreflexive _ F.Rel }

namespace Hilbert.KTc.Kripke

instance sound : Sound (Hilbert.KTc) Kripke.FrameClass.corefl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_corefl _ rfl;
  exact Kripke.validate_AxiomTc_of_coreflexive (corefl := F_corefl);

instance consistent : Entailment.Consistent (Hilbert.KTc) := consistent_of_sound_frameclass Kripke.FrameClass.corefl $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.KTc) FrameClass.corefl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KTc) FrameClass.corefl := inferInstance

end Hilbert.KTc.Kripke

end LO.Modal

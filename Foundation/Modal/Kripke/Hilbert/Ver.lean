import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.isolated : FrameClass := { F | IsIsolated _ F }

namespace Hilbert.Ver

instance Kripke.sound : Sound (Hilbert.Ver) FrameClass.isolated := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F hF _ (rfl | rfl);
  have := Set.mem_setOf_eq.mp hF;
  exact Kripke.validate_AxiomVer_of_isolated (F := F);

instance Kripke.consistent : Entailment.Consistent (Hilbert.Ver) := consistent_of_sound_frameclass FrameClass.isolated $ by
  use blackpoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Kripke.Canonical (Hilbert.Ver) FrameClass.isolated := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance Kripke.complete : Complete (Hilbert.Ver) FrameClass.isolated := inferInstance

end Hilbert.Ver

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.refl : FrameClass := { F | IsRefl _ F }

namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) Kripke.FrameClass.refl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_refl _ rfl;
  exact Kripke.validate_AxiomT_of_reflexive (refl := F_refl);

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) := consistent_of_sound_frameclass Kripke.FrameClass.refl $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance Kripke.canonical : Canonical (Hilbert.KT) Kripke.FrameClass.refl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance Kripke.complete : Complete (Hilbert.KT) Kripke.FrameClass.refl := inferInstance

end Hilbert.KT

end LO.Modal

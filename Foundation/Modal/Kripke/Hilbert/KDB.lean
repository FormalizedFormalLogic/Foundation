import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_symm : FrameClass := { F | IsSerial _ F ∧ IsSymm _ F }

namespace Hilbert.KDB.Kripke

instance sound : Sound (Hilbert.KDB) Kripke.FrameClass.serial_symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomB_of_symmetric;

instance consistent : Entailment.Consistent (Hilbert.KDB) := consistent_of_sound_frameclass Kripke.FrameClass.serial_symm $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KDB) Kripke.FrameClass.serial_symm := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KDB) Kripke.FrameClass.serial_symm := inferInstance

end Hilbert.KDB.Kripke

end LO.Modal

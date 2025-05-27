import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Hilbert.WellKnown
namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_eucl : FrameClass := { F | IsSerial _ F ∧ IsEuclidean _ F }

namespace Hilbert.KD5.Kripke

instance sound : Sound (Hilbert.KD5) Kripke.FrameClass.serial_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KD5) := consistent_of_sound_frameclass Kripke.FrameClass.serial_eucl $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KD5) Kripke.FrameClass.serial_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KD5) Kripke.FrameClass.serial_eucl := inferInstance

end Hilbert.KD5.Kripke

lemma Logic.KD5.Kripke.serial_eucl : Logic.KD5 = FrameClass.serial_eucl.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

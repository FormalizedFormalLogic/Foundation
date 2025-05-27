import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans_eucl : FrameClass := { F | IsSerial _ F ∧ IsTrans _ F ∧ IsEuclidean _ F }

namespace Hilbert.KD45.Kripke

instance sound : Sound (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KD45) := consistent_of_sound_frameclass Kripke.FrameClass.serial_trans_eucl $ by
  use whitepoint;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;
⟩

instance complete : Complete (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := inferInstance

end Hilbert.KD45.Kripke

lemma Logic.KD45.Kripke.serial_trans_eucl : Logic.KD45 = FrameClass.serial_trans_eucl.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

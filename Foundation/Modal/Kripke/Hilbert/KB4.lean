import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_trans : FrameClass := { F | IsSymm _ F ∧ IsTrans _ F }

namespace Hilbert.KB4.Kripke

instance sound : Sound (Hilbert.KB4) Kripke.FrameClass.symm_trans := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.KB4) := consistent_of_sound_frameclass Kripke.FrameClass.symm_trans $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KB4) Kripke.FrameClass.symm_trans := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KB4) Kripke.FrameClass.symm_trans := inferInstance

end Hilbert.KB4.Kripke

lemma Logic.KB4.Kripke.refl_trans : Logic.KB4 = FrameClass.symm_trans.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

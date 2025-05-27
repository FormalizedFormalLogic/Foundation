import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.trans_eucl : FrameClass := { F | IsTrans _ F ∧ IsEuclidean _ F }

namespace Hilbert.K45.Kripke

instance sound : Sound (Hilbert.K45) FrameClass.trans_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.K45) := consistent_of_sound_frameclass Kripke.FrameClass.trans_eucl $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.K45) FrameClass.trans_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.K45) FrameClass.trans_eucl := inferInstance

end Hilbert.K45.Kripke

lemma Logic.K45.Kripke.trans_eucl : Logic.K45 = FrameClass.trans_eucl.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

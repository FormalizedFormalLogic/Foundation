import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_eucl : FrameClass := { F | IsSymm _ F ∧ IsEuclidean _ F }

namespace Hilbert.KB5.Kripke

instance sound : Sound (Hilbert.KB5) Kripke.FrameClass.symm_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KB5) := consistent_of_sound_frameclass Kripke.FrameClass.symm_eucl $ by
  use whitepoint;
  constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KB5) Kripke.FrameClass.symm_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KB5) Kripke.FrameClass.symm_eucl := inferInstance


end Hilbert.KB5.Kripke

end LO.Modal

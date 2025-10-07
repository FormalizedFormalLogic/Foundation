import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected class Frame.IsKB5 (F : Kripke.Frame) extends F.IsSymmetric, F.IsEuclidean
protected abbrev FrameClass.KB5 : FrameClass := { F | F.IsKB5 }

end Kripke

instance : Sound (Modal.KB5) Kripke.FrameClass.KB5 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFive_of_euclidean;

instance : Entailment.Consistent (Modal.KB5) := consistent_of_sound_frameclass Kripke.FrameClass.KB5 $ by
  use whitepoint;
  constructor;

instance : Canonical (Modal.KB5) Kripke.FrameClass.KB5 := ⟨by constructor⟩

instance : Complete (Modal.KB5) Kripke.FrameClass.KB5 := inferInstance

end LO.Modal

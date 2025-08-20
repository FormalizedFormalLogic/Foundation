import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected class Frame.IsKB5 (F : Kripke.Frame) extends F.IsSymmetric, F.IsEuclidean
protected abbrev FrameClass.KB5 : FrameClass := { F | F.IsKB5 }

end Kripke


namespace Logic.KB5.Kripke

instance : Sound (Hilbert.KB5) Kripke.FrameClass.KB5 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  simp only [Set.mem_singleton_iff, forall_eq]
  rintro F ⟨_, _⟩ _ (rfl | rfl)
  . exact validate_AxiomB_of_symmetric
  . exact validate_AxiomFive_of_euclidean

instance : Entailment.Consistent (Hilbert.KB5) := consistent_of_sound_frameclass Kripke.FrameClass.KB5 $ by
  use whitepoint
  constructor


instance : Canonical (Hilbert.KB5) Kripke.FrameClass.KB5 := ⟨by constructor⟩

instance : Complete (Hilbert.KB5) Kripke.FrameClass.KB5 := inferInstance

end Logic.KB5.Kripke


end LO.Modal

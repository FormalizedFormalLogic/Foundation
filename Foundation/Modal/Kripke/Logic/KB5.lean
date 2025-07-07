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

instance sound : Sound (Hilbert.KB5) Kripke.FrameClass.KB5 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KB5) := consistent_of_sound_frameclass Kripke.FrameClass.KB5 $ by
  use whitepoint;
  constructor;


instance canonical : Canonical (Hilbert.KB5) Kripke.FrameClass.KB5 := ⟨by constructor⟩

instance complete : Complete (Hilbert.KB5) Kripke.FrameClass.KB5 := inferInstance

end Logic.KB5.Kripke

lemma Logic.KB5.Kripke.symm : Logic.KB5 = Kripke.FrameClass.KB5.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

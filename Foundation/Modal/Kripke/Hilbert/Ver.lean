import Foundation.Modal.Kripke.AxiomVer
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

protected abbrev isolated : FrameClass := { F | Isolated F }

namespace isolated

@[simp]
lemma nonempty : FrameClass.isolated.Nonempty := by
  use ⟨Unit, λ _ _ => False⟩;
  tauto;

lemma validates_AxiomVer : FrameClass.isolated.ValidatesFormula (Axioms.Ver (.atom 0)) := by
  simp [Validates];
  intro F;
  apply validate_AxiomVer_of_isolated;

lemma validates_HilbertVer : FrameClass.isolated.Validates Hilbert.Ver.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomVer;

end isolated

end Kripke.FrameClass


namespace Hilbert.Ver

instance Kripke.sound : Sound (Hilbert.Ver) FrameClass.isolated :=
  instSound_of_validates_axioms FrameClass.isolated.validates_HilbertVer

instance Kripke.consistent : Entailment.Consistent (Hilbert.Ver) :=
  consistent_of_sound_frameclass FrameClass.isolated (by simp)

instance : Kripke.Canonical (Hilbert.Ver) FrameClass.isolated := ⟨Canonical.isolated⟩

instance Kripke.complete : Complete (Hilbert.Ver) FrameClass.isolated := inferInstance

end Hilbert.Ver

end LO.Modal

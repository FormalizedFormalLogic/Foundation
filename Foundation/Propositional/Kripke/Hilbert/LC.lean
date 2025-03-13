import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev connected : FrameClass := { F | Connected F }

namespace connected

@[simp]
instance nonempty : FrameClass.connected.Nonempty := by
  use whitepoint;
  simp [Connected];

lemma validates_AxiomWLEM : FrameClass.connected.ValidatesFormula (Axioms.Dummett (.atom 0) (.atom 1)) := by
  rintro F _ _ rfl;
  apply validate_Dummett_of_connected $ by assumption

instance validate_HilbertLC : FrameClass.connected.Validates (Hilbert.LC.axioms) := by
  apply FrameClass.Validates.withAxiomEFQ;
  apply validates_AxiomWLEM;

end connected

end Kripke.FrameClass


namespace Hilbert.LC.Kripke

instance sound : Sound Hilbert.LC FrameClass.connected :=
  instSound_of_validates_axioms FrameClass.connected.validate_HilbertLC

instance consistent : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.connected (by simp)

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨Canonical.connected⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

end Hilbert.LC.Kripke

end LO.Propositional

import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.AxiomLEM

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev euclidean : FrameClass := { F | Euclidean F }

namespace euclidean

@[simp]
instance nonempty : FrameClass.euclidean.Nonempty := by
  use whitepoint;
  simp [Euclidean];

lemma validates_AxiomLEM : FrameClass.euclidean.ValidatesFormula (Axioms.LEM (.atom 0)) := by
  rintro F _ _ rfl;
  apply validate_LEM_of_euclidean $ by assumption

instance validate_HilbertLC : FrameClass.euclidean.Validates (Hilbert.Cl.axioms) := by
  apply FrameClass.Validates.withAxiomEFQ;
  apply validates_AxiomLEM;

end euclidean

end Kripke.FrameClass


namespace Hilbert.Cl.Kripke

instance sound : Sound Hilbert.Cl FrameClass.euclidean :=
  instSound_of_validates_axioms FrameClass.euclidean.validate_HilbertLC

instance consistent : Entailment.Consistent Hilbert.Cl := consistent_of_sound_frameclass FrameClass.euclidean (by simp)

instance canonical : Canonical Hilbert.Cl FrameClass.euclidean := ⟨Canonical.euclidean⟩

instance complete : Complete Hilbert.Cl FrameClass.euclidean := inferInstance

end Hilbert.Cl.Kripke


end LO.Propositional

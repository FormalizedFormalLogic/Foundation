import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev confluent : FrameClass := { F | Confluent F }

namespace confluent

@[simp]
instance nonempty : FrameClass.confluent.Nonempty := by
  use whitepoint;
  simp [Confluent];

lemma validates_AxiomWLEM : FrameClass.confluent.ValidatesFormula (Axioms.WeakLEM (.atom 0)) := by
  rintro F _ _ rfl;
  apply validate_WeakLEM_of_confluent $ by assumption

instance validate_HilbertKC : FrameClass.confluent.Validates (Hilbert.KC.axioms) := by
  apply FrameClass.Validates.withAxiomEFQ;
  apply validates_AxiomWLEM;

end confluent

end Kripke.FrameClass


namespace Hilbert.KC.Kripke

instance sound : Sound Hilbert.KC FrameClass.confluent :=
  instSound_of_validates_axioms FrameClass.confluent.validate_HilbertKC

instance consistent : Entailment.Consistent Hilbert.KC := consistent_of_sound_frameclass FrameClass.confluent (by simp)

instance canonical : Canonical Hilbert.KC FrameClass.confluent := ⟨Canonical.confluent⟩

instance complete : Complete Hilbert.KC FrameClass.confluent := inferInstance

end Hilbert.KC.Kripke

end LO.Propositional

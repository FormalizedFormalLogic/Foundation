import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Filteration
import Foundation.Propositional.Kripke.Rooted

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev confluent : FrameClass := { F | IsConfluent _ F }
protected abbrev finite_confluent : FrameClass := { F | Finite F ∧ IsConfluent _ F }

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


namespace finite_confluent

instance validate_HilbertKC : FrameClass.finite_confluent.Validates (Hilbert.KC.axioms) := by
  apply FrameClass.Validates.withAxiomEFQ;
  rintro F ⟨_, _⟩ _ rfl;
  apply FrameClass.confluent.validate_HilbertKC;
  repeat tauto;

end finite_confluent

end Kripke.FrameClass


namespace Hilbert.KC.Kripke

instance sound : Sound Hilbert.KC FrameClass.confluent := instSound_of_validates_axioms FrameClass.confluent.validate_HilbertKC

instance sound_finite : Sound Hilbert.KC FrameClass.finite_confluent :=
  instSound_of_validates_axioms FrameClass.finite_confluent.validate_HilbertKC

instance consistent : Entailment.Consistent Hilbert.KC := consistent_of_sound_frameclass FrameClass.confluent (by simp)

instance canonical : Canonical Hilbert.KC FrameClass.confluent := ⟨Canonical.confluent⟩

instance complete : Complete Hilbert.KC FrameClass.confluent := inferInstance

section FFP

open
  finestFilterationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.KC) FrameClass.finite_confluent := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_con V r;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFilterationTransitiveClosureModel RM (φ.subformulas);
  apply filteration FRM finestFilterationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
    . simp only [exists_and_left, and_self];
      use ⟦⟨z, by tauto⟩⟧;
      apply Relation.TransGen.single;
      use ⟨z, by tauto⟩;
      constructor;
      . tauto;
      . use ⟨z, by tauto⟩;
        constructor;
        . tauto;
        . apply F.refl;
    . use ⟦⟨z, by tauto⟩⟧;
      constructor;
      . apply TransGen.single;
        use ⟨y, by tauto⟩, ⟨z, by tauto⟩;
        tauto;
      . apply Frame.refl;
    . use ⟦⟨y, by tauto⟩⟧;
      constructor;
      . apply Frame.refl;
      . apply TransGen.single;
        use ⟨z, by tauto⟩, ⟨y, by tauto⟩;
        tauto;
    . obtain ⟨u, Ryu, Rzu⟩ := F_con ⟨Rry, Rrz⟩;
      have : r ≺ u := F.trans Rry Ryu;
      use ⟦⟨u, by tauto⟩⟧;
      constructor;
      . apply TransGen.single;
        use ⟨y, by tauto⟩, ⟨u, by tauto⟩;
        tauto;
      . apply TransGen.single;
        use ⟨z, by tauto⟩, ⟨u, by tauto⟩;
        tauto;
⟩

end FFP


end Hilbert.KC.Kripke

end LO.Propositional

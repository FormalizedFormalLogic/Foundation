import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomLEM
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Filtration
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Rooted

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev euclidean : FrameClass := { F | IsEuclidean _ F }
protected abbrev finite_symmetric : FrameClass := { F | Finite F ∧ IsSymm _ F }
protected abbrev finite_euclidean : FrameClass := { F | Finite F ∧ IsEuclidean _ F }

lemma eq_finite_euclidean_finite_symmetric : FrameClass.finite_euclidean = FrameClass.finite_symmetric := by
  ext F;
  constructor;
  . rintro ⟨_, hF⟩; exact ⟨by tauto, inferInstance⟩;
  . rintro ⟨_, hF⟩; exact ⟨by tauto, inferInstance⟩;

end Kripke.FrameClass


namespace Hilbert.Cl.Kripke

instance sound_finite : Sound Hilbert.Cl FrameClass.finite_symmetric :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_LEM_of_symmetric;

instance sound_finite_symmetric : Sound Hilbert.Cl FrameClass.finite_symmetric :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_LEM_of_symmetric;

instance sound_euclidean : Sound Hilbert.Cl FrameClass.euclidean :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_LEM_of_euclidean;

instance sound_finite_euclidean : Sound Hilbert.Cl FrameClass.finite_euclidean :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_LEM_of_euclidean;


instance consistent : Entailment.Consistent Hilbert.Cl := consistent_of_sound_frameclass FrameClass.euclidean $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.Cl FrameClass.euclidean :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.Cl FrameClass.euclidean := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance complete_finite_symmetric : Complete (Hilbert.Cl) FrameClass.finite_symmetric := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_con V r;
  replace F_con := Set.mem_setOf_eq.mp F_con;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;

  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite; simp;
  . apply isSymm_iff _ _ |>.mpr;
    rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ RXY;
    . simp_all;
    . apply TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . have : y ≺ x := IsSymm.symm _ _ Rry;
        tauto;
    . apply TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . have : x ≺ y := IsSymm.symm _ _ Rrx;
        tauto;
    . apply Relation.TransGen.single;
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩;
      refine ⟨by tauto, by tauto, ?_⟩;
      . have : y ≺ x := IsEuclidean.euclidean Rrx Rry;
        tauto;
⟩

instance complete_finite_euclidean : Complete (Hilbert.Cl) FrameClass.finite_euclidean := by
  convert complete_finite_symmetric;
  exact FrameClass.eq_finite_euclidean_finite_symmetric;

end FFP

end Hilbert.Cl.Kripke


end LO.Propositional

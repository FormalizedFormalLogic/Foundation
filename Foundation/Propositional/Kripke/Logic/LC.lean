import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Logic.KC

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke

variable {F : Frame}
protected abbrev Frame.IsLC := Frame.IsPiecewiseStronglyConnected
protected class Frame.IsFiniteLC (F : Frame) extends F.IsFinite, F.IsLC

protected abbrev FrameClass.LC : FrameClass := { F | F.IsLC }
protected abbrev FrameClass.finite_LC : FrameClass := { F | F.IsFiniteLC }

end Kripke


namespace Hilbert.LC.Kripke

instance sound : Sound Hilbert.LC FrameClass.LC := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomDummett_of_isPiecewiseStronglyConnected;

instance sound_finite : Sound Hilbert.LC FrameClass.finite_LC :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomDummett_of_isPiecewiseStronglyConnected;

instance consistent : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.LC $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.LC FrameClass.LC := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.LC FrameClass.LC := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.LC) FrameClass.finite_LC := ⟨by
  intro φ hφ;
  apply Kripke.complete.complete;
  rintro F F_conn V r;
  replace F_conn := Set.mem_setOf_eq.mp F_conn;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;
  exact {
    world_finite := by
      apply FilterEqvQuotient.finite;
      simp;
    ps_connected := by
      rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ;
      . simp only [exists_and_left, or_self];
        apply Relation.TransGen.single
        use ⟨z, by tauto⟩;
        constructor;
        . tauto
        . use ⟨z, by tauto⟩;
          constructor;
          . tauto;
          . exact F.refl;
      . left;
        apply Relation.TransGen.single;
        use ⟨y, by tauto⟩, ⟨z, by tauto⟩;
        tauto;
      . right;
        apply Relation.TransGen.single;
        use ⟨z, by tauto⟩, ⟨y, by tauto⟩;
        tauto;
      . let Y : RM.World := ⟨y, by tauto⟩;
        let Z : RM.World := ⟨z, by tauto⟩;
        rcases F.ps_connected Rry Rrz with (Ryz | Rrw);
        . left;
          apply Relation.TransGen.single;
          use Y, Z;
          tauto;
        . right;
          apply Relation.TransGen.single;
          use Z, Y;
          tauto;
  }

⟩

end FFP

end Hilbert.LC.Kripke

namespace Logic.LC


lemma Kripke.LC : Logic.LC = Kripke.FrameClass.LC.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Kripke.finite_LC : Logic.LC = Kripke.FrameClass.finite_LC.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

@[simp]
theorem proper_extension_of_KC : Logic.KC ⊂ Logic.LC := by
  constructor;
  . exact (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp)).subset
  . suffices ∃ φ, Hilbert.LC ⊢! φ ∧ ¬FrameClass.KC ⊧ φ by rw [KC.Kripke.KC]; tauto;
    use Axioms.Dummett (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply not_validOnFrameClass_of_exists_frame;
      use {
        World := Fin 4
        Rel := λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      constructor;
      . refine {
          ps_convergent := by
            intros x y z Rxy Ryz;
            use 3;
            omega;
        }
      . apply not_imp_not.mpr $ isPiecewiseStronglyConnected_of_validate_axiomDummett;
        by_contra hC;
        simpa using @hC.ps_connected 0 1 2;


end Logic.LC

end LO.Propositional

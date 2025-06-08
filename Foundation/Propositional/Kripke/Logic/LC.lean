import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Logic.KC

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke.FrameClass

protected abbrev connected : FrameClass := { F | IsConnected _ F }
protected abbrev finite_connected : FrameClass := { F | Finite F ∧ IsConnected _ F }

end Kripke.FrameClass


namespace Hilbert.LC.Kripke

instance sound : Sound Hilbert.LC FrameClass.connected := instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_Dummett_of_connected

instance sound_finite : Sound Hilbert.LC FrameClass.finite_connected :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_Dummett_of_connected

instance consistent : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.connected $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.LC) FrameClass.finite_connected := ⟨by
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

  refine ⟨?_, ?_⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . apply isConnected_iff _ _ |>.mpr;
    rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ ⟨RXY, RXZ⟩;
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
      rcases IsConnected.connected ⟨Rry, Rrz⟩ with (Ryz | Rrw);
      . left;
        apply Relation.TransGen.single;
        use Y, Z;
        tauto;
      . right;
        apply Relation.TransGen.single;
        use Z, Y;
        tauto;
⟩

end FFP

end Hilbert.LC.Kripke

namespace Logic.LC


lemma Kripke.connected : Logic.LC = Kripke.FrameClass.connected.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Kripke.finite_connected : Logic.LC = Kripke.FrameClass.finite_connected.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

@[simp]
theorem proper_extension_of_KC : Logic.KC ⊂ Logic.LC := by
  constructor;
  . exact (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp)).subset
  . suffices ∃ φ, Hilbert.LC ⊢! φ ∧ ¬FrameClass.confluent ⊧ φ by
      rw [KC.Kripke.confluent];
      tauto;
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
      . apply isConfluent_iff _ _ |>.mpr
        simp only [Confluent, Fin.isValue, not_and, and_imp];
        intros;
        use 3;
        omega;
      . apply not_imp_not.mpr $ Kripke.connected_of_validate_Dummett;
        unfold Connected;
        push_neg;
        use 0, 1, 2;
        simp;

end Logic.LC

end LO.Propositional

import Foundation.Propositional.Kripke.AxiomLEM
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Logic.LC
import Foundation.Propositional.Kripke.Logic.KP

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke


namespace Kripke

variable {F : Frame}

protected abbrev Frame.IsCl := Frame.IsEuclidean
protected class Frame.IsFiniteCl (F : Frame) extends F.IsFinite, F.IsCl

instance : whitepoint.IsEuclidean := ⟨by tauto⟩

protected abbrev FrameClass.Cl : FrameClass := { F | F.IsCl }
protected abbrev FrameClass.finite_Cl : FrameClass := { F | F.IsFiniteCl }

instance [F.IsCl] : F.IsKP := ⟨by
  rintro x y z ⟨Rxy, Rxz, Ryz, _⟩;
  exfalso;
  apply Ryz;
  exact F.eucl Rxy Rxz;
⟩

end Kripke



namespace Hilbert.Cl.Kripke

instance sound : Sound Hilbert.Cl FrameClass.Cl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomLEM_of_isEuclidean;

instance sound_finite : Sound Hilbert.Cl FrameClass.finite_Cl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F ⟨_, hF⟩ _ rfl;
    apply validate_axiomLEM_of_isEuclidean;

instance consistent : Entailment.Consistent Hilbert.Cl := consistent_of_sound_frameclass FrameClass.Cl $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance canonical : Canonical Hilbert.Cl FrameClass.Cl :=  ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.Cl FrameClass.Cl := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance complete_finite_symmetric : Complete (Hilbert.Cl) FrameClass.finite_Cl := by
  suffices Complete (Hilbert.Cl) { F : Frame | F.IsFinite ∧ F.IsSymmetric } by
    convert this;
    constructor;
    . rintro ⟨_, hF⟩; exact ⟨by tauto, inferInstance⟩;
    . rintro ⟨_, hF⟩; exact {}

  constructor;
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
  . exact {
      world_finite := by
        apply FilterEqvQuotient.finite;
        simp;
    };
  . constructor;
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
      . simpa using F.eucl' Rrx Rry;

end FFP

end Hilbert.Cl.Kripke


namespace Logic.Cl

lemma Kripke.Cl : Logic.Cl = FrameClass.Cl.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Kripke.finite_Cl : Logic.Cl = FrameClass.finite_Cl.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

@[simp]
theorem proper_extension_of_LC : Logic.LC ⊂ Logic.Cl := by
  constructor;
  . apply (Hilbert.weakerThan_of_dominate_axiomInstances
      (by rintro _ ⟨ψ, ⟨(rfl | rfl), ⟨s, rfl⟩⟩⟩ <;> simp)).subset;
  . suffices ∃ φ, Hilbert.Cl ⊢! φ ∧ ¬FrameClass.LC ⊧ φ by rw [LC.Kripke.LC]; tauto;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 2,
        Rel := λ x y => x ≤ y
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      use F;
      constructor;
      . refine { ps_connected := by intro x y z; omega; }
      . apply not_imp_not.mpr $ Kripke.isEuclidean_of_validate_axiomLEM;
        by_contra hC;
        have := @F.eucl _ 0 1 0;
        omega;

@[simp]
lemma proper_extension_of_Int : Logic.Int ⊂ Logic.Cl := by
  trans Logic.LC;
  trans Logic.KC;
  all_goals simp;

@[simp]
theorem proper_extension_of_KP : Logic.KP ⊂ Logic.Cl := by
  constructor;
  . rw [KP.Kripke.KP, Cl.Kripke.Cl];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . suffices ∃ φ, Hilbert.Cl ⊢! φ ∧ ¬FrameClass.KP ⊧ φ by rw [KP.Kripke.KP]; tauto;
    use Axioms.LEM (.atom 0);
    constructor;
    . simp;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 3,
        Rel := λ x y => x = 0 ∨ x = y
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      use F;
      constructor;
      . refine {
          kriesel_putnam := by
            rintro x y z ⟨Rxy, Rxz, nRyz, nRzy⟩;
            match x, y, z with
            | _, 0, 0 => simp_all;
            | _, 1, 1 => simp_all;
            | _, 2, 2 => simp_all;
            | 1, _, 2 => omega;
            | 2, _, 1 => omega;
            | 0, 0, _ => omega;
            | 0, 1, 0 => omega;
            | 0, 1, 2 =>
              use 0;
              refine ⟨by tauto, by tauto, by tauto, ?_⟩;
              intro u hu;
              match u with
              | 0 => use 1; tauto;
              | 1 => use 1; tauto;
              | 2 => use 2; tauto;
            | 0, 2, 0 => omega;
            | 0, 2, 1 =>
              use 0;
              refine ⟨by tauto, by tauto, by tauto, ?_⟩;
              intro u hu;
              match u with
              | 0 => use 1; tauto;
              | 1 => use 1; tauto;
              | 2 => use 2; tauto;
        }
      . apply not_imp_not.mpr $ Kripke.isEuclidean_of_validate_axiomLEM;
        by_contra hC;
        have := @F.eucl _ 0 1 0;
        omega;

end Logic.Cl


end LO.Propositional

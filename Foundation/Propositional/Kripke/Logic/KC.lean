module

public import Foundation.Propositional.Kripke.AxiomWLEM
public import Foundation.Propositional.Kripke.Rooted
public import Foundation.Propositional.Kripke.Logic.KrieselPutnam


@[expose] public section

namespace LO.Propositional

open Kripke
open Modal.Kripke
open Formula.Kripke


namespace Kripke

variable {F : Frame}

@[reducible] protected alias Frame.IsKC := Frame.IsPiecewiseStronglyConvergent
protected class Frame.IsFiniteKC (F : Frame) extends F.IsFinite, F.IsKC

protected abbrev FrameClass.KC : FrameClass := { F | F.IsPiecewiseStronglyConvergent }
protected abbrev FrameClass.finite_KC : FrameClass := { F | F.IsFiniteKC }

instance [F.IsKC] : F.IsKrieselPutnam := ⟨by
  rintro x y z ⟨Rxy, Rxz, nRyz, nRzy⟩;
  use x;
  refine ⟨F.refl, Rxy, Rxz, ?_⟩;
  intro v Rxv;
  obtain ⟨u, Ryu, Rvu⟩ := F.ps_convergent Rxy Rxv;
  use u;
  tauto;
⟩

end Kripke


namespace KC

instance : Sound Propositional.KC FrameClass.KC :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomWLEM_of_isPiecewiseStronglyConvergent

instance : Sound Propositional.KC FrameClass.finite_KC :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomWLEM_of_isPiecewiseStronglyConvergent

instance : Entailment.Consistent Propositional.KC := consistent_of_sound_frameclass FrameClass.KC $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical Propositional.KC FrameClass.KC := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Propositional.KC FrameClass.KC := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance : Complete (Propositional.KC) FrameClass.finite_KC := ⟨by
  intro φ hφ;
  apply Complete.complete (𝓜 := FrameClass.KC);
  rintro F F_con V r;
  replace F_con := Set.mem_setOf_eq.mp F_con;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;
  exact {
    world_finite := by apply FilterEqvQuotient.finite; simp;
    ps_convergent := by
      rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ;
      . simp only [exists_and_left, and_self];
        let Z : RM.World := ⟨z, by tauto⟩;
        use ⟦Z⟧;
        apply Relation.TransGen.single;
        use Z;
        constructor;
        . tauto;
        . use Z;
          constructor;
          . tauto;
          . apply F.refl;
      . let Y : RM.World := ⟨y, by tauto⟩;
        let Z : RM.World := ⟨z, by tauto⟩;
        use ⟦Z⟧;
        constructor;
        . apply TransGen.single;
          use Y, Z;
          tauto;
        . apply Frame.refl;
      . let Y : RM.World := ⟨y, by tauto⟩;
        let Z : RM.World := ⟨z, by tauto⟩;
        use ⟦Y⟧;
        constructor;
        . apply Frame.refl;
        . apply TransGen.single;
          use Z, Y;
          tauto;
      . obtain ⟨u, Ryu, Rzu⟩ := F.ps_convergent Rry Rrz;
        have : r ≺ u := F.trans Rry Ryu;
        let Y : RM.World := ⟨y, by tauto⟩;
        let Z : RM.World := ⟨z, by tauto⟩;
        let U : RM.World := ⟨u, by tauto⟩;
        use ⟦U⟧;
        constructor;
        . apply TransGen.single;
          use Y, U;
          tauto;
        . apply TransGen.single;
          use Z, U;
          tauto;
  }
⟩

end FFP

end KC


instance : Propositional.KrieselPutnam ⪱ Propositional.KC := by
  constructor;
  . apply weakerThan_of_subset_frameClass FrameClass.KrieselPutnam FrameClass.KC;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.WLEM (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KrieselPutnam)
      apply not_validOnFrameClass_of_exists_frame;
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
            | 0, 1, 2
            | 0, 2, 1 =>
              use 0;
              refine ⟨by tauto, by tauto, by tauto, ?_⟩;
              intro u hu;
              match u with
              | 0 => use 1; tauto;
              | 1 => use 1; tauto;
              | 2 => use 2; tauto;
            | _, 0, 0
            | _, 1, 1
            | _, 2, 2
            | 1, _, 2
            | 2, _, 1
            | 0, 0, _
            | 0, 1, 0
            | 0, 2, 0 => omega;
        }
      . apply not_imp_not.mpr $ Kripke.isPiecewiseStronglyConvergent_of_validate_axiomWLEM;
        by_contra hC;
        have := @F.ps_convergent _ 0 1 2;
        omega;

instance : Propositional.Int ⪱ Propositional.KC := calc
  Propositional.Int ⪱ Propositional.KrieselPutnam := inferInstance
  _   ⪱ Propositional.KC := inferInstance

end LO.Propositional
end

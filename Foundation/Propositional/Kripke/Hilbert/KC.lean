module

public import Foundation.Propositional.Kripke.AxiomWLEM
public import Foundation.Propositional.Kripke.Hilbert.KreiselPutnam
public import Foundation.Propositional.Kripke.Rooted

@[expose] public section

namespace LO.Propositional.Hilbert

open Kripke
open Formula.Kripke

namespace KC

instance : ({ F : Frame | F.IsPiecewiseStronglyConvergent }) ⊧* (Hilbert.KC : Hilbert ℕ) := by
  constructor;
  rintro φ (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩) F hF <;>
  replace hF := Set.mem_setOf_eq.mp hF;
  . grind;
  . exact validate_axiomWLEM_of_isPiecewiseStronglyConvergent;

instance : Entailment.Consistent (Hilbert.KC : Hilbert ℕ) := consistent_of_nonempty_frameClass ({ F : Frame | F.IsPiecewiseStronglyConvergent }) $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical (Hilbert.KC : Hilbert ℕ) ({ F : Frame | F.IsPiecewiseStronglyConvergent }) := by
  constructor;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance instKripkeComplete : Complete (Hilbert.KC : Hilbert ℕ) ({ F : Frame | F.IsPiecewiseStronglyConvergent }) := inferInstance

open finestFiltrationTransitiveClosureModel Relation in
instance instKripkeCompleteFinite : Complete (Hilbert.KC : Hilbert ℕ) ({ F : Frame | Finite F ∧ F.IsPiecewiseStronglyConvergent }) := by
  constructor;
  intro φ hφ;
  apply Complete.complete (𝓜 := ({ F : Frame | F.IsPiecewiseStronglyConvergent }));
  rintro F F_conn V r;
  replace F_conn := Set.mem_setOf_eq.mp F_conn;
  let M : Kripke.Model := ⟨F, V⟩;
  let RM := M↾r;

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp;

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas);
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr;
  apply hφ;
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ⟨?_⟩⟩;
  . apply FilterEqvQuotient.finite;
    simp;
  . rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ;
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

end KC


instance {F : Kripke.Frame} [F.IsPiecewiseStronglyConvergent] : F.SatisfiesKreiselPutnamCondition := by
  constructor;
  rintro x y z ⟨Rxy, Rxz, nRyz, nRzy⟩;
  use x;
  refine ⟨F.refl, Rxy, Rxz, ?_⟩;
  intro v Rxv;
  obtain ⟨u, Ryu, Rvu⟩ := F.ps_convergent Rxy Rxv;
  use u;
  tauto;

instance : (Hilbert.KreiselPutnam : Hilbert ℕ) ⪱ Hilbert.KC := by
  constructor;
  . apply weakerThan_of_subset_frameClass ({ F | F.SatisfiesKreiselPutnamCondition }) ({ F | F.IsPiecewiseStronglyConvergent });
    apply Set.setOf_subset_setOf.mpr;
    intro F hF;
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.WLEM (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := ({ F : Frame | F.SatisfiesKreiselPutnamCondition }))
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
      . constructor;
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
      . apply not_imp_not.mpr $ Kripke.isPiecewiseStronglyConvergent_of_validate_axiomWLEM;
        by_contra hC;
        have := @F.ps_convergent _ 0 1 2;
        omega;

end LO.Propositional.Hilbert

end

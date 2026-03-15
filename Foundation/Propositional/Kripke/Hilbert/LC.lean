module

public import Foundation.Propositional.Kripke.AxiomDummett
public import Foundation.Propositional.Kripke.Hilbert.KC
public import Foundation.Propositional.Kripke.Rooted

@[expose] public section

namespace LO.Propositional.Hilbert

open Kripke
open Formula.Kripke

namespace LC

instance : ({ F : Frame | F.IsPiecewiseStronglyConnected }) ⊧* (Hilbert.LC : Hilbert ℕ) := by
  constructor;
  rintro φ (⟨_, rfl⟩ | ⟨_, _, _, rfl⟩) F hF <;>
  replace hF := Set.mem_setOf_eq.mp hF;
  . grind;
  . exact validate_axiomDummett_of_isPiecewiseStronglyConnected;

instance : Entailment.Consistent (Hilbert.LC : Hilbert ℕ) := consistent_of_nonempty_frameClass ({ F : Frame | F.IsPiecewiseStronglyConnected }) $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Canonical (Hilbert.LC : Hilbert ℕ) ({ F : Frame | F.IsPiecewiseStronglyConnected }) := by
  constructor;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Complete (Hilbert.LC : Hilbert ℕ) ({ F : Frame | F.IsPiecewiseStronglyConnected }) := inferInstance

open finestFiltrationTransitiveClosureModel Relation in
instance : Complete (Hilbert.LC : Hilbert ℕ) ({ F : Frame | Finite F ∧ F.IsPiecewiseStronglyConnected }) := by
  constructor;
  intro φ hφ;
  apply Complete.complete (𝓜 := ({ F : Frame | F.IsPiecewiseStronglyConnected }));
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

end LC

instance : (Hilbert.KC : Hilbert ℕ) ⪱ Hilbert.LC := by
  constructor;
  . apply weakerThan_of_subset_frameClass ({ F | F.IsPiecewiseStronglyConvergent }) ({ F | F.IsPiecewiseStronglyConnected });
    apply Set.setOf_subset_setOf.mpr;
    intro F hF;
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Dummett (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := ({ F : Frame | F.IsPiecewiseStronglyConvergent }))
      apply not_validOnFrameClass_of_exists_frame;
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
      . constructor;
        intros x y z Rxy Ryz;
        use 3;
        omega;
      . apply not_imp_not.mpr $ isPiecewiseStronglyConnected_of_validate_axiomDummett;
        by_contra hC;
        simpa using @hC.ps_connected 0 1 2;

end LO.Propositional.Hilbert

end

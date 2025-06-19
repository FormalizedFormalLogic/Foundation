import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Rooted
import Foundation.Propositional.Kripke.Logic.Int


namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke

protected abbrev Frame.IsKC := Frame.IsPiecewiseStronglyConvergent
protected class Frame.IsFiniteKC (F : Frame) extends F.IsFinite, F.IsKC

protected abbrev FrameClass.KC : FrameClass := { F | F.IsKC }
protected abbrev FrameClass.finite_KC : FrameClass := { F | F.IsFiniteKC }

end Kripke


namespace Hilbert.KC.Kripke

instance sound : Sound Hilbert.KC FrameClass.KC :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomWeakLEM_of_isPiecewiseStronglyConvergent

instance sound_finite : Sound Hilbert.KC FrameClass.finite_KC :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ;
    rintro F hF _ rfl;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply validate_axiomWeakLEM_of_isPiecewiseStronglyConvergent

instance consistent : Entailment.Consistent Hilbert.KC := consistent_of_sound_frameclass FrameClass.KC $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical Hilbert.KC FrameClass.KC := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete Hilbert.KC FrameClass.KC := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance finite_complete : Complete (Hilbert.KC) FrameClass.finite_KC := ⟨by
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

end Hilbert.KC.Kripke

namespace Logic.KC

open Kripke
open Entailment
open Formula.Kripke

lemma Kripke.KC : Logic.KC = FrameClass.KC.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic
lemma Kripke.finite_KC : Logic.KC = FrameClass.finite_KC.logic := eq_Hilbert_Logic_KripkeFrameClass_Logic

@[simp]
theorem proper_extension_of_Int : Logic.Int ⊂ Logic.KC := by
  constructor;
  . exact (Hilbert.weakerThan_of_subset_axioms (by simp)).subset;
  . suffices ∃ φ, Hilbert.KC ⊢! φ ∧ ¬FrameClass.all ⊧ φ by rw [Int.Kripke.Int]; tauto;
    use Axioms.WeakLEM (.atom 0);
    constructor;
    . exact wlem!;
    . apply not_validOnFrameClass_of_exists_frame;
      let F : Frame := {
        World := Fin 3
        Rel := λ x y => x = 0 ∨ (x = y)
        rel_partial_order := {
          refl := by omega;
          trans := by omega;
          antisymm := by omega;
        }
      };
      use F;
      constructor;
      . tauto;
      . apply not_imp_not.mpr $ isPiecewiseStronglyConvergent_of_validate_axiomWeakLEM;
        by_contra hC;
        have := @F.ps_convergent _ 0 1 2;
        omega;

end Logic.KC

end LO.Propositional

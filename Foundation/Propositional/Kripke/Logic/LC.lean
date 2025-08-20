import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Logic.KC

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke

namespace Kripke

variable {F : Frame}

@[reducible] protected alias Frame.IsLC := Frame.IsPiecewiseStronglyConnected
protected class Frame.IsFiniteLC (F : Frame) extends F.IsFinite, F.IsLC

protected abbrev FrameClass.LC : FrameClass := { F | F.IsLC }
protected abbrev FrameClass.finite_LC : FrameClass := { F | F.IsFiniteLC }

end Kripke


namespace Hilbert

namespace LC.Kripke

instance : Sound Hilbert.LC FrameClass.LC := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomEFQ
  rintro F hF _ rfl
  replace hF := Set.mem_setOf_eq.mp hF
  apply validate_axiomDummett_of_isPiecewiseStronglyConnected

instance : Sound Hilbert.LC FrameClass.finite_LC := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomEFQ
  rintro F hF _ rfl
  replace hF := Set.mem_setOf_eq.mp hF
  apply validate_axiomDummett_of_isPiecewiseStronglyConnected

instance : Entailment.Consistent Hilbert.LC := consistent_of_sound_frameclass FrameClass.LC $ by
  use whitepoint
  apply Set.mem_setOf_eq.mpr
  infer_instance

instance : Canonical Hilbert.LC FrameClass.LC := ⟨by
  apply Set.mem_setOf_eq.mpr
  infer_instance
⟩

instance : Complete Hilbert.LC FrameClass.LC := inferInstance

open finestFiltrationTransitiveClosureModel Relation in
instance : Complete Hilbert.LC FrameClass.finite_LC := ⟨by
  intro φ hφ
  apply Complete.complete (𝓜 := FrameClass.LC)
  rintro F F_conn V r
  replace F_conn := Set.mem_setOf_eq.mp F_conn
  let M : Kripke.Model := ⟨F, V⟩
  let RM := M↾r

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas)
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr
  apply hφ
  exact {
    world_finite := by
      apply FilterEqvQuotient.finite
      simp
    ps_connected := by
      rintro X ⟨y, (rfl | Rry)⟩ ⟨z, (rfl | Rrz)⟩ RXY RXZ
      . simp only [exists_and_left, or_self]
        apply Relation.TransGen.single
        use ⟨z, by tauto⟩
        constructor
        . tauto
        . use ⟨z, by tauto⟩
          constructor
          . tauto
          . exact F.refl
      . left
        apply Relation.TransGen.single
        use ⟨y, by tauto⟩, ⟨z, by tauto⟩
        tauto
      . right
        apply Relation.TransGen.single
        use ⟨z, by tauto⟩, ⟨y, by tauto⟩
        tauto
      . let Y : RM.World := ⟨y, by tauto⟩
        let Z : RM.World := ⟨z, by tauto⟩
        rcases F.ps_connected Rry Rrz with (Ryz | Rrw)
        . left
          apply Relation.TransGen.single
          use Y, Z
          tauto
        . right
          apply Relation.TransGen.single
          use Z, Y
          tauto
  }
⟩

end LC.Kripke

instance : Hilbert.KC ⪱ Hilbert.LC := by
  constructor
  . apply weakerThan_of_subset_frameClass FrameClass.KC FrameClass.LC
    intro F hF
    simp_all only [Set.mem_setOf_eq]
    infer_instance
  . apply Entailment.not_weakerThan_iff.mpr
    use Axioms.Dummett (.atom 0) (.atom 1)
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KC)
      apply not_validOnFrameClass_of_exists_frame
      use {
        World := Fin 4
        Rel := λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)
        rel_partial_order := {
          refl := by omega
          trans := by omega
          antisymm := by omega
        }
      }
      constructor
      . refine {
          ps_convergent := by
            intros x y z Rxy Ryz
            use 3
            omega
        }
      . apply not_imp_not.mpr $ isPiecewiseStronglyConnected_of_validate_axiomDummett
        by_contra hC
        simpa using @hC.ps_connected 0 1 2

end Hilbert


propositional_kripke 𝐋𝐂 FrameClass.LC
propositional_kripke 𝐋𝐂 FrameClass.finite_LC

instance : 𝐊𝐂 ⪱ 𝐋𝐂 := inferInstance


end LO.Propositional

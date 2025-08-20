import Foundation.Propositional.Kripke.AxiomLEM
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Logic.LC

namespace LO.Propositional

open Kripke
open Hilbert.Kripke
open Formula.Kripke


namespace Kripke

variable {F : Frame}

@[reducible] protected alias Frame.IsCl := Frame.IsEuclidean
protected class Frame.IsFiniteCl (F : Frame) extends F.IsFinite, F.IsCl

instance : whitepoint.IsEuclidean := ⟨by tauto⟩

protected abbrev FrameClass.Cl : FrameClass := { F | F.IsCl }
protected abbrev FrameClass.finite_Cl : FrameClass := { F | F.IsFiniteCl }

instance [F.IsCl] : F.IsKrieselPutnam := ⟨by
  rintro x y z ⟨Rxy, Rxz, Ryz, _⟩
  exfalso
  apply Ryz
  exact F.eucl Rxy Rxz
⟩

end Kripke



namespace Hilbert

namespace Cl.Kripke

instance : Sound Hilbert.Cl FrameClass.Cl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ
    rintro F hF _ rfl
    replace hF := Set.mem_setOf_eq.mp hF
    apply validate_axiomLEM_of_isEuclidean

instance : Sound Hilbert.Cl FrameClass.finite_Cl :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomEFQ
    rintro F ⟨_, hF⟩ _ rfl
    apply validate_axiomLEM_of_isEuclidean

instance : Entailment.Consistent Hilbert.Cl := consistent_of_sound_frameclass FrameClass.Cl $ by
  use whitepoint
  apply Set.mem_setOf_eq.mpr
  infer_instance

instance : Canonical Hilbert.Cl FrameClass.Cl :=  ⟨by
  apply Set.mem_setOf_eq.mpr
  infer_instance
⟩

instance : Complete Hilbert.Cl FrameClass.Cl := inferInstance

section FFP

open
  finestFiltrationTransitiveClosureModel
  Relation

instance : Complete Hilbert.Cl FrameClass.finite_Cl := by
  suffices Complete Hilbert.Cl { F : Frame | F.IsFinite ∧ F.IsSymmetric } by
    convert this
    constructor
    . rintro ⟨_, hF⟩; exact ⟨by tauto, inferInstance⟩
    . rintro ⟨_, hF⟩; exact {}

  constructor
  intro φ hφ
  apply Complete.complete (𝓜 := FrameClass.Cl)
  rintro F F_con V r
  replace F_con := Set.mem_setOf_eq.mp F_con
  let M : Kripke.Model := ⟨F, V⟩
  let RM := M↾r

  apply Model.pointGenerate.modal_equivalent_at_root (M := M) (r := r) |>.mp

  let FRM := finestFiltrationTransitiveClosureModel RM (φ.subformulas)
  apply filtration FRM finestFiltrationTransitiveClosureModel.filterOf (by simp) |>.mpr
  apply hφ

  refine ⟨?_, ?_⟩
  . exact {
      world_finite := by
        apply FilterEqvQuotient.finite
        simp
    }
  . constructor
    rintro ⟨x, (rfl | Rrx)⟩ ⟨y, (rfl | Rry)⟩ RXY
    . simp_all
    . apply TransGen.single
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩
      refine ⟨by tauto, by tauto, ?_⟩
      . have : y ≺ x := IsSymm.symm _ _ Rry
        tauto
    . apply TransGen.single
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩
      refine ⟨by tauto, by tauto, ?_⟩
      . have : x ≺ y := IsSymm.symm _ _ Rrx
        tauto
    . apply Relation.TransGen.single
      use ⟨y, by tauto⟩, ⟨x, by tauto⟩
      refine ⟨by tauto, by tauto, ?_⟩
      . simpa using F.eucl' Rrx Rry

end FFP

end Cl.Kripke

instance : Hilbert.LC ⪱ Hilbert.Cl := by
  constructor
  . apply Hilbert.weakerThan_of_provable_axioms
    rintro φ (rfl | rfl) <;> simp
  . apply Entailment.not_weakerThan_iff.mpr
    use Axioms.LEM (.atom 0)
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.LC)
      apply not_validOnFrameClass_of_exists_frame
      let F : Frame := {
        World := Fin 2,
        Rel := λ x y => x ≤ y
        rel_partial_order := {
          refl := by omega
          trans := by omega
          antisymm := by omega
        }
      }
      use F
      constructor
      . refine { ps_connected := by intro x y z; omega; }
      . apply not_imp_not.mpr $ Kripke.isEuclidean_of_validate_axiomLEM
        by_contra hC
        have := @F.eucl _ 0 1 0
        omega

instance : Hilbert.Int ⪱ Hilbert.Cl := calc
  Hilbert.Int ⪱ Hilbert.KC := inferInstance
  _           ⪱ Hilbert.LC := inferInstance
  _           ⪱ Hilbert.Cl := inferInstance

end Hilbert

propositional_kripke 𝐂𝐥 FrameClass.Cl
propositional_kripke 𝐂𝐥 FrameClass.finite_Cl

instance : 𝐋𝐂 ⪱ 𝐂𝐥 := inferInstance
instance : 𝐈𝐧𝐭 ⪱ 𝐂𝐥 := inferInstance

end LO.Propositional

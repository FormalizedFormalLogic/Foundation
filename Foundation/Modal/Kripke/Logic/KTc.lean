import Foundation.Modal.Kripke.Logic.KB4


namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsKTc := Frame.IsCoreflexive

protected abbrev FrameClass.KTc : FrameClass := { F | F.IsKTc }

instance [F.IsKTc] : F.IsKB4 where

end Kripke




namespace Hilbert.KTc.Kripke

instance : Sound (Hilbert.KTc) Kripke.FrameClass.KTc := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  simp only [Set.mem_singleton_iff, forall_eq]
  rintro F F_corefl
  exact Kripke.validate_AxiomTc_of_coreflexive (corefl := F_corefl)

instance : Entailment.Consistent (Hilbert.KTc) := consistent_of_sound_frameclass Kripke.FrameClass.KTc $ by
  use whitepoint
  apply Set.mem_setOf_eq.mpr
  infer_instance

instance : Canonical (Hilbert.KTc) Kripke.FrameClass.KTc := ⟨by
  apply Set.mem_setOf_eq.mpr
  infer_instance
⟩

instance : Complete (Hilbert.KTc) Kripke.FrameClass.KTc := inferInstance


instance : Hilbert.KB4 ⪱ Hilbert.KTc := by
  constructor
  . apply Hilbert.Kripke.weakerThan_of_subset_frameClass FrameClass.KB4 FrameClass.KTc
    intro F hF
    simp_all only [Set.mem_setOf_eq]
    infer_instance
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.Tc (.atom 0))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.KB4)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩
      use M, 0
      constructor
      . exact {
          symm := by simp [M],
          trans := by simp [M],
        }
      . suffices ∃ x, (x : M.World) ≠ 0 by
          simp [M, Semantics.Realize, Satisfies]
          tauto
        use 1
        aesop

end Hilbert.KTc.Kripke

instance : Modal.KB4 ⪱ Modal.KTc := inferInstance

end LO.Modal

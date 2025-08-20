import Foundation.Modal.Kripke.Logic.S4Point2McK
import Foundation.Modal.Kripke.Logic.S4Point3

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point3McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.IsPiecewiseConnected, F.SatisfiesMcKinseyCondition where

instance [F.IsS4Point3McK] : F.IsS4Point2McK where

protected abbrev FrameClass.S4Point3McK : FrameClass := { F | F.IsS4Point3McK }

end Kripke


namespace Hilbert.S4Point3McK.Kripke

instance : Sound (Hilbert.S4Point3McK) FrameClass.S4Point3McK := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  rintro _ (rfl | rfl | rfl | rfl) F ⟨_, _⟩
  . exact validate_AxiomT_of_reflexive
  . exact validate_AxiomFour_of_transitive
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected

instance : Entailment.Consistent Hilbert.S4Point3McK :=
  consistent_of_sound_frameclass FrameClass.S4Point3McK $ by
    use whitepoint
    constructor

instance : Canonical (Hilbert.S4Point3McK) FrameClass.S4Point3McK := ⟨by constructor⟩

instance : Complete (Hilbert.S4Point3McK) FrameClass.S4Point3McK := inferInstance


instance : Hilbert.S4Point2McK ⪱ Hilbert.S4Point3McK := by
  constructor
  . apply Hilbert.Kripke.weakerThan_of_subset_frameClass FrameClass.S4Point2McK FrameClass.S4Point3McK
    intro F hF
    simp_all only [Set.mem_setOf_eq]
    infer_instance
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.Point3 (.atom 0) (.atom 1))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point2McK)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      let M : Model := ⟨
        ⟨Fin 4, λ x y => x = 0 ∨ y = 3 ∨ x = y⟩,
        λ w a => match a with | 0 => w = 1 ∨ w = 3 | 1 => w = 2 ∨ w = 3 | _ => False
      ⟩
      use M, 0
      constructor
      . refine {
          refl := by omega,
          trans := by omega,
          mckinsey := by
            intro x
            use 3
            simp [Frame.Rel', M]
          ps_convergent := by
            intro x y z Rxy Ryz
            use 3
            tauto
        }
      . suffices
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 1 ∨ w = 3) ∧ x ≠ 2 ∧ x ≠ 3) ∧
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 2 ∨ w = 3) ∧ x ≠ 1 ∧ x ≠ 3) by
          simp [M, Semantics.Realize, Satisfies]
          tauto
        constructor
        . use 1; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
        . use 2; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

instance : Hilbert.S4Point3 ⪱ Hilbert.S4Point3McK := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.McK (.atom 0))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point3)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩
      use M, 0
      constructor
      . exact {
          refl := by tauto,
          trans := by tauto,
          ps_connected := by tauto
        }
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies]
        use 1
        trivial

end Hilbert.S4Point3McK.Kripke

instance : Modal.S4Point2McK ⪱ Modal.S4Point3McK := inferInstance

instance : Modal.S4Point3 ⪱ Modal.S4Point3McK := inferInstance

end LO.Modal

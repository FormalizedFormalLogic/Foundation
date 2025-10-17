import Foundation.Modal.Kripke.AxiomGrz
import Foundation.Modal.Kripke.Logic.S4McK
import Mathlib.Order.Preorder.Finite

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGrz (F : Frame) extends F.IsFinite, F.IsPartialOrder

protected abbrev FrameClass.finite_Grz: FrameClass := { F | F.IsFiniteGrz }

instance : whitepoint.IsAntisymmetric := ⟨by tauto⟩
instance : whitepoint.IsFiniteGrz where

instance [F.IsFinite] [F.IsPartialOrder] : F.SatisfiesMcKinseyCondition where
  mckinsey := by
    intro x;
    obtain ⟨y, _, Rxy, hy₃⟩ :=  @Finite.exists_le_maximal _ {
      le := F,
      le_refl := fun a ↦ Frame.refl,
      le_trans := fun x y z ↦ Frame.trans
    } _ (λ y => x ≺ y) x Frame.refl;
    use y;
    constructor;
    . tauto;
    . intro z Ryz;
      apply F.antisymm;
      . assumption;
      . exact @hy₃ z (F.trans Rxy Ryz) Ryz;
instance [F.IsFiniteGrz] : F.IsS4McK where

end Kripke

instance : Sound Modal.Grz FrameClass.finite_Grz := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  exact validate_AxiomGrz_of_refl_trans_wcwf;

instance : Entailment.Consistent Modal.Grz :=
  consistent_of_sound_frameclass FrameClass.finite_Grz $ by
    use whitepoint;
    constructor;

end LO.Modal

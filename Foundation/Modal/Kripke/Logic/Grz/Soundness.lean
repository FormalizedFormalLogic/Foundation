import Foundation.Modal.Kripke.AxiomGrz
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.S4M
import Mathlib.Order.Preorder.Finite

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGrz (F : Frame) extends F.IsFinite, F.IsPartialOrder

protected abbrev FrameClass.finite_Grz: FrameClass := { F | F.IsFiniteGrz }

instance : whitepoint.IsAntisymmetric := ⟨by tauto⟩
instance : whitepoint.IsFiniteGrz where

instance [F.IsFiniteGrz] : F.SatisfiesMcKinseyCondition where
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
instance [F.IsFiniteGrz] : F.IsS4M where

end Kripke


namespace Hilbert.Grz.Kripke

instance finite_sound : Sound (Hilbert.Grz) FrameClass.finite_Grz := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ rfl;
  exact validate_AxiomGrz_of_refl_trans_wcwf;

instance consistent : Entailment.Consistent (Hilbert.Grz) :=
  consistent_of_sound_frameclass FrameClass.finite_Grz $ by
    use whitepoint;
    constructor;

end Hilbert.Grz.Kripke

end LO.Modal

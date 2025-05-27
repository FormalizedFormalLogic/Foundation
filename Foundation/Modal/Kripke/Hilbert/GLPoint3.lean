import Foundation.Modal.Kripke.Hilbert.GL.Completeness
import Foundation.Modal.Kripke.AxiomWeakPoint3

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

abbrev FrameClass.finite_strict_linear_order : FrameClass := { F | Finite F.World ∧ IsStrictOrder _ F.Rel ∧ IsWeakConnected _ F.Rel }

end Kripke


namespace Hilbert.GLPoint3.Kripke

instance finite_sound : Sound (Hilbert.GLPoint3) FrameClass.finite_strict_linear_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance consistent : Entailment.Consistent (Hilbert.GLPoint3) :=
  consistent_of_sound_frameclass FrameClass.finite_strict_linear_order $ by
    use blackpoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance finite_complete : Complete (Hilbert.GLPoint3) (FrameClass.finite_strict_linear_order) := by sorry;

end Hilbert.GLPoint3.Kripke

lemma Logic.GLPoint3.Kripke.finite_strict_linear_order : Logic.GLPoint3 = FrameClass.finite_strict_linear_order.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

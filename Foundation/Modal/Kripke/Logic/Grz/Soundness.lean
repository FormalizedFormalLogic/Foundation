import Foundation.Modal.Kripke.AxiomGrz

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev FrameClass.trans_wcwf : FrameClass := { F | F.IsPreorder.Rel ∧ IsWeaklyConverseWellFounded _ F.Rel }
protected abbrev FrameClass.finite_partial_order: FrameClass := { F | F.IsFinite ∧ IsPartialOrder _ F.Rel }

end Kripke


namespace Hilbert.Grz.Kripke

instance finite_sound : Sound (Hilbert.Grz) FrameClass.finite_partial_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ rfl;
  exact validate_AxiomGrz_of_refl_trans_wcwf;

instance consistent : Entailment.Consistent (Hilbert.Grz) :=
  consistent_of_sound_frameclass FrameClass.finite_partial_order $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    exact ⟨inferInstance, inferInstance⟩

end Hilbert.Grz.Kripke

end LO.Modal

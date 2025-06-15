import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

abbrev Kripke.FrameClass.trans_cwf : FrameClass := { F | F.IsTransitive.Rel ∧ IsConverseWellFounded _ F.Rel }

abbrev Kripke.FrameClass.finite_trans_irrefl: FrameClass := { F | Finite F.World ∧ F.IsTransitive.Rel ∧ IsIrrefl _ F.Rel }


namespace Hilbert.GL.Kripke

instance finite_sound : Sound (Hilbert.GL) FrameClass.finite_trans_irrefl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ rfl;
  exact validate_AxiomL_of_trans_cwf;

instance consistent : Entailment.Consistent (Hilbert.GL) :=
  consistent_of_sound_frameclass FrameClass.finite_trans_irrefl $ by
    use blackpoint;
    apply Set.mem_setOf_eq.mpr;
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end Hilbert.GL.Kripke

end LO.Modal

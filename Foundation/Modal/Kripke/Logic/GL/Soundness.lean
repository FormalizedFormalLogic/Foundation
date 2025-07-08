import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Entailment
open Formula
open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGL (F : Frame) extends F.IsFinite, F.IsStrictPreorder

protected abbrev FrameClass.finite_GL: FrameClass := { F | F.IsFiniteGL }

instance : blackpoint.IsFiniteGL where

end Kripke


namespace Logic.GL.Kripke

instance finite_sound : Sound Hilbert.GL FrameClass.finite_GL := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ rfl;
  exact validate_AxiomL_of_trans_cwf;

instance consistent : Entailment.Consistent Hilbert.GL :=
  consistent_of_sound_frameclass FrameClass.finite_GL $ by
    use blackpoint;
    constructor;

end Logic.GL.Kripke


instance : Entailment.Consistent Modal.GL := inferInstance

end LO.Modal

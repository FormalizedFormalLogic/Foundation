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

protected class Frame.IsInfiniteGL (F : Frame) extends F.IsTransitive, F.IsConverseWellFounded

protected class Frame.IsFiniteGL (F : Frame) extends F.IsFinite, F.IsStrictPreorder

protected abbrev FrameClass.infinite_GL: FrameClass := { F | F.IsInfiniteGL }

protected abbrev FrameClass.finite_GL: FrameClass := { F | F.IsFiniteGL }

instance : blackpoint.IsFiniteGL where

end Kripke


namespace Logic.GL.Kripke

instance : Sound Hilbert.GL Kripke.FrameClass.infinite_GL := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F ⟨_, _⟩;
  exact validate_AxiomL_of_trans_cwf;

instance : Sound Hilbert.GL FrameClass.finite_GL := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F ⟨_, _, _⟩;
  exact validate_AxiomL_of_trans_cwf;

instance : Entailment.Consistent Hilbert.GL :=
  consistent_of_sound_frameclass FrameClass.finite_GL $ by
    use blackpoint;
    constructor;

end Logic.GL.Kripke


instance : Entailment.Consistent Modal.GL := inferInstance

end LO.Modal

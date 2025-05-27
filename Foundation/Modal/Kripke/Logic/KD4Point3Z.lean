import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Logic.Soundness
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.LinearFrame
import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.AxiomGeach

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Hilbert.Kripke

namespace Hilbert.KD4Point3Z.Kripke

instance sound_natLT : Sound Hilbert.KD4Point3Z natLT := instSound_of_frame_validates_axioms $ by
  simp only [Semantics.RealizeSet.insert_iff, ValidOnFrame.models_iff, Semantics.RealizeSet.singleton_iff];
  refine ⟨?_, ?_, ?_, ?_, ?_⟩;
  . apply FrameClass.all.validates_axiomK <;> tauto;
  . apply validate_AxiomD_of_serial;
  . apply validate_AxiomFour_of_transitive;
  . apply validate_WeakPoint3_of_weakConnected;
  . apply Kripke.natLT_validates_AxiomZ;

instance consistent : Entailment.Consistent (Hilbert.KD4Point3Z) := consistent_of_sound_frames natLT

end Hilbert.KD4Point3Z.Kripke

end LO.Modal

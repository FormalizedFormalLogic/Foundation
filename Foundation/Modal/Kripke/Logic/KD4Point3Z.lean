module

public import Foundation.Modal.Kripke.AxiomL
public import Foundation.Modal.Kripke.LinearFrame
public import Foundation.Modal.Kripke.AxiomWeakPoint3
public import Foundation.Modal.Kripke.AxiomGeach
public import Foundation.Modal.Kripke.Logic.KD4

@[expose] public section

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke
open Modal.Kripke

instance : Sound Modal.KD4Point3Z natLT := instSound_of_frame_validates_axioms $ by
  suffices
    ValidOnFrame natLT (Axioms.K (atom 0) (atom 1)) ∧
    ValidOnFrame natLT (Axioms.D (atom 0)) ∧
    ValidOnFrame natLT (Axioms.Four (atom 0)) ∧
    ValidOnFrame natLT (Axioms.WeakPoint3 (atom 0) (atom 1)) ∧
    ValidOnFrame natLT (Axioms.Z (atom 0)) by
    simpa [Semantics.ModelsSet.insert_iff, ValidOnFrame.models_iff, Semantics.ModelsSet.singleton_iff];
  refine ⟨?_, ?_, ?_, ?_, ?_⟩;
  . tauto;
  . apply validate_AxiomD_of_serial;
  . apply validate_AxiomFour_of_transitive;
  . apply validate_WeakPoint3_of_weakConnected;
  . apply Kripke.natLT_validates_AxiomZ;

instance : Entailment.Consistent Modal.KD4Point3Z := consistent_of_sound_frames natLT

end LO.Modal
end

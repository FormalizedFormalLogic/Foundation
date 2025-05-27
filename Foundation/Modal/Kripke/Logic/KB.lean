import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean


protected abbrev Kripke.FrameClass.symm : FrameClass := { F | IsSymm _ F }

namespace Hilbert.KB.Kripke

instance sound : Sound (Hilbert.KB) Kripke.FrameClass.symm := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F F_symm _ rfl;
  exact validate_AxiomB_of_symmetric (sym := F_symm);

instance consistent : Entailment.Consistent (Hilbert.KB) := consistent_of_sound_frameclass FrameClass.symm $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance canonical : Canonical (Hilbert.KB) Kripke.FrameClass.symm := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KB) Kripke.FrameClass.symm := inferInstance

end Hilbert.KB.Kripke

lemma Logic.KB.Kripke.symm : Logic.KB = FrameClass.symm.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

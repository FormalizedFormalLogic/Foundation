import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean


namespace Kripke.FrameClass

protected abbrev symm : FrameClass := { F | Symmetric F }

namespace symm

lemma isMultiGeachean : FrameClass.symm = FrameClass.multiGeachean {⟨0, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.symm.Nonempty := by simp [isMultiGeachean]

lemma validates_AxiomB : FrameClass.symm.ValidatesFormula (Axioms.B (.atom 0)) := by
  rintro F F_symm _ rfl;
  apply validate_AxiomB_of_symmetric $ by assumption

lemma validates_HilbertKB : FrameClass.symm.Validates Hilbert.KB.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomB;

end symm

end Kripke.FrameClass


namespace Hilbert.KB

instance Kripke.sound : Sound (Hilbert.KB) Kripke.FrameClass.symm :=
  instSound_of_validates_axioms FrameClass.symm.validates_HilbertKB

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB) :=
  consistent_of_sound_frameclass FrameClass.symm (by simp)

instance Kripke.canonical : Canonical (Hilbert.KB) Kripke.FrameClass.symm := ⟨Canonical.symmetric⟩

instance Kripke.complete : Complete (Hilbert.KB) Kripke.FrameClass.symm := inferInstance

end Hilbert.KB

end LO.Modal

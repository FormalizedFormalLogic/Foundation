import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

protected abbrev corefl : FrameClass := { F | Coreflexive F }

namespace corefl

lemma isMultiGeachean : FrameClass.corefl = FrameClass.multiGeachean {⟨0, 1, 0, 0⟩} := by
  ext F;
  simp [Geachean.coreflexive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.corefl.Nonempty := by simp [corefl.isMultiGeachean]

lemma validates_AxiomTc : FrameClass.corefl.ValidatesFormula (Axioms.Tc (.atom 0)) := by
  rintro F F_corefl _ rfl;
  apply validate_AxiomTc_of_coreflexive F_corefl;

lemma validates_HilbertKTc : FrameClass.corefl.Validates Hilbert.KTc.axioms := Validates.withAxiomK validates_AxiomTc

end corefl

end Kripke.FrameClass

namespace Hilbert.KTc

instance Kripke.sound : Sound (Hilbert.KTc) Kripke.FrameClass.corefl :=
  instSound_of_validates_axioms Kripke.FrameClass.corefl.validates_HilbertKTc

instance Kripke.consistent : Entailment.Consistent (Hilbert.KTc) :=
  consistent_of_sound_frameclass Kripke.FrameClass.corefl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KTc) FrameClass.corefl := ⟨Canonical.coreflexive⟩

instance Kripke.complete : Complete (Hilbert.KTc) FrameClass.corefl := inferInstance

end Hilbert.KTc


end LO.Modal

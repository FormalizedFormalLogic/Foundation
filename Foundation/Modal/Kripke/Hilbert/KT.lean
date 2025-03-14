import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

protected abbrev refl : FrameClass := { F | Reflexive F }


namespace refl

lemma isMultiGeachean : FrameClass.refl = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩} := by
  ext F;
  simp [Geachean.reflexive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.refl.Nonempty := by simp [refl.isMultiGeachean]

lemma validates_AxiomT : FrameClass.refl.ValidatesFormula (Axioms.T (.atom 0)) := by
  rintro F F_refl _ rfl;
  apply validate_AxiomT_of_reflexive $ by assumption

lemma validates_HilbertKT : FrameClass.refl.Validates Hilbert.KT.axioms := Validates.withAxiomK validates_AxiomT

end refl

end Kripke.FrameClass


namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) Kripke.FrameClass.refl :=
  instSound_of_validates_axioms Kripke.FrameClass.refl.validates_HilbertKT

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) :=
  consistent_of_sound_frameclass Kripke.FrameClass.refl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KT) Kripke.FrameClass.refl := ⟨Canonical.reflexive⟩

instance Kripke.complete : Complete (Hilbert.KT) Kripke.FrameClass.refl := inferInstance

end Hilbert.KT

end LO.Modal

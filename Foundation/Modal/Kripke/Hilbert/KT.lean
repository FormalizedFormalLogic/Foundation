import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke

variable {F : Frame}

protected abbrev FrameClass.refl : FrameClass := { F | IsRefl _ F }

namespace FrameClass.refl

@[simp] lemma nonempty : FrameClass.refl.Nonempty := by use whitepoint; tauto;

lemma validates_AxiomT : FrameClass.refl.ValidatesFormula (Axioms.T (.atom 0)) := by
  apply ValidatesFormula_of;
  apply Kripke.validate_AxiomT_of_reflexive;

lemma validates_HilbertKT : FrameClass.refl.Validates Hilbert.KT.axioms := Validates.withAxiomK validates_AxiomT

end FrameClass.refl

end Kripke


namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) Kripke.FrameClass.refl :=
  instSound_of_validates_axioms Kripke.FrameClass.refl.validates_HilbertKT

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) :=
  consistent_of_sound_frameclass Kripke.FrameClass.refl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KT) Kripke.FrameClass.refl := ⟨Canonical.reflexive⟩

instance Kripke.complete : Complete (Hilbert.KT) Kripke.FrameClass.refl := inferInstance

end Hilbert.KT

end LO.Modal

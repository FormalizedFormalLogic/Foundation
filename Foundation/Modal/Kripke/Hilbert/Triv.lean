import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.KTc

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.refl_corefl : FrameClass := { F | Reflexive F ∧ Coreflexive F }
protected abbrev Kripke.FrameClass.equality : FrameClass := { F | Equality F }

namespace Kripke.FrameClass.refl_corefl

lemma isMultiGeachean : FrameClass.refl_corefl = FrameClass.multiGeachean {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩} := by
  ext F;
  simp [Geachean.reflexive_def, Geachean.coreflexive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.refl_corefl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertTriv : Kripke.FrameClass.refl_corefl.Validates Hilbert.Triv.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_refl, F_trans⟩ φ (rfl | rfl);
  . apply FrameClass.refl.validates_AxiomT; repeat tauto;
  . apply FrameClass.corefl.validates_AxiomTc; repeat tauto;

end Kripke.FrameClass.refl_corefl


lemma Kripke.FrameClass.eq_equality_refl_corefl : Kripke.FrameClass.equality = Kripke.FrameClass.refl_corefl := by
  ext F;
  constructor;
  . intro hEq;
    constructor;
    . exact refl_of_equality hEq;
    . exact corefl_of_equality hEq;
  . rintro ⟨hRefl, hCorefl⟩;
    exact equality_of_refl_corefl hRefl hCorefl;


namespace Hilbert.Triv

instance Kripke.sound_refl_corefl : Sound (Hilbert.Triv) Kripke.FrameClass.refl_corefl :=
  instSound_of_validates_axioms Kripke.FrameClass.refl_corefl.validates_HilbertTriv

instance Kripke.sound_equality : Sound (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  exact Kripke.sound_refl_corefl;

instance Kripke.consistent : Entailment.Consistent (Hilbert.Triv) :=
  consistent_of_sound_frameclass Kripke.FrameClass.refl_corefl (by simp)

instance Kripke.cannonical_refl_corefl : Canonical (Hilbert.Triv) Kripke.FrameClass.refl_corefl := ⟨⟨Canonical.reflexive, Canonical.coreflexive⟩⟩

instance Kripke.complete_refl_corefl : Complete (Hilbert.Triv) Kripke.FrameClass.refl_corefl := inferInstance

instance Kripke.complete_equality : Complete (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  exact Kripke.complete_refl_corefl;

end Hilbert.Triv


end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

protected abbrev Kripke.FrameClass.refl_corefl : FrameClass := { F | Reflexive F ∧ Coreflexive F }
protected abbrev Kripke.FrameClass.equality : FrameClass := { F | Equality F }

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

instance Kripke.sound_refl_corefl : Sound (Hilbert.Triv) Kripke.FrameClass.refl_corefl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  exact eq_Geach;
  . unfold Kripke.FrameClass.refl_corefl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance Kripke.sound_equality : Sound (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  exact Kripke.sound_refl_corefl;

instance Kripke.consistent : Entailment.Consistent (Hilbert.Triv) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  exact eq_Geach;

instance Kripke.cannonical_refl_corefl : Canonical (Hilbert.Triv) Kripke.FrameClass.refl_corefl := ⟨⟨Canonical.reflexive, Canonical.coreflexive⟩⟩

instance Kripke.complete_refl_corefl : Complete (Hilbert.Triv) Kripke.FrameClass.refl_corefl := inferInstance

instance Kripke.complete_equality : Complete (Hilbert.Triv) Kripke.FrameClass.equality := by
  rw [Kripke.FrameClass.eq_equality_refl_corefl];
  exact Kripke.complete_refl_corefl;

end Hilbert.Triv


end LO.Modal

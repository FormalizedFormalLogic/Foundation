import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveCoreflexiveFrameClass : FrameClass := { F | Reflexive F ∧ Coreflexive F }
abbrev Kripke.EqualityFrameClass : FrameClass := { F | Equality F }

lemma Kripke.eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass : EqualityFrameClass = ReflexiveCoreflexiveFrameClass := by
  ext F;
  constructor;
  . intro hEq;
    constructor;
    . exact refl_of_equality hEq;
    . exact corefl_of_equality hEq;
  . rintro ⟨hRefl, hCorefl⟩;
    exact equality_of_refl_corefl hRefl hCorefl;


namespace Hilbert.Triv

instance Kripke.Consistent : System.Consistent (Hilbert.Triv) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  exact eq_Geach;

instance Kripke.CompleteReflCorefl : Complete (Hilbert.Triv) (Kripke.ReflexiveCoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveCoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance Kripke.CompleteEquality : Complete (Hilbert.Triv) (Kripke.EqualityFrameClass) := by
  rw [eq_EqualityFrameClass_ReflexiveCoreflexiveFrameClass];
  exact Kripke.CompleteReflCorefl;

end Hilbert.Triv


end LO.Modal

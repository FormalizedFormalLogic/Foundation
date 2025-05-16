import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.AxiomM

namespace LO.Modal

open Kripke
open Geachean

instance : TransitiveMcKinseyanFrameClass.DefinedBy Hilbert.K4Point1.axioms :=
  FrameClass.definedBy_with_axiomK $ TransitiveMcKinseyanFrameClass.DefinedByFourAndM

namespace Hilbert.K4Point1

instance Kripke.sound : Sound (Hilbert.K4Point1) (Kripke.TransitiveMcKinseyanFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Point1) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.TransitiveMcKinseyanFrameClass

open
  Kripke
  MaximalConsistentSet
in
instance Kripke.canonical : Canonical (Hilbert.K4Point1) TransitiveMcKinseyanFrameClass := by
  have hK4 := canonicalFrame.multigeachean_of_provable_geach (G := {⟨0, 2, 1, 0⟩}) (𝓢 := Hilbert.K4Point1) (by simp);
  constructor;
  refine ⟨?_, ?_⟩;
  . simpa [transitive_def] using @hK4 (⟨0, 2, 1, 0⟩) $ by tauto;
  . sorry;

instance Kripke.complete : Complete (Hilbert.K4Point1) TransitiveMcKinseyanFrameClass := inferInstance

end Hilbert.K4Point1

end LO.Modal

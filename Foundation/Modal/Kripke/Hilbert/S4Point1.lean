import Foundation.Modal.Kripke.Hilbert.KT
import Foundation.Modal.Kripke.Hilbert.K4Point1

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveMcKinseyanFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ McKinseyan F }

instance : ReflexiveTransitiveMcKinseyanFrameClass.DefinedBy Hilbert.S4Point1.axioms := by
  rw [
    (show ReflexiveTransitiveMcKinseyanFrameClass = TransitiveMcKinseyanFrameClass ∩ ReflexiveFrameClass by aesop),
    (show Hilbert.S4Point1.axioms = Hilbert.K4Point1.axioms ∪ {Axioms.T (.atom 0)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.TransitiveMcKinseyanFrameClass (Hilbert.K4Point1.axioms) ReflexiveFrameClass {Axioms.T (.atom 0)};

instance : Kripke.ReflexiveTransitiveMcKinseyanFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, McKinseyan];


namespace Hilbert.S4Point1

instance Kripke.sound : Sound (Hilbert.S4Point1) (Kripke.ReflexiveTransitiveMcKinseyanFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4Point1) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.ReflexiveTransitiveMcKinseyanFrameClass

instance Kripke.complete : Complete (Hilbert.S4Point1) ReflexiveTransitiveMcKinseyanFrameClass := by sorry;

end Hilbert.S4Point1

end LO.Modal

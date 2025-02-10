import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomDot3

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveConnectedFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

instance Kripke.ReflexiveTransitiveConnectedFrameClass.DefinedByS4Dot3Axioms
  : FrameClass.DefinedBy Kripke.ReflexiveTransitiveConnectedFrameClass Hilbert.S4Dot3.axioms := by
  rw [
    (show ReflexiveTransitiveConnectedFrameClass = ReflexiveTransitiveFrameClass ∩ ConnectedFrameClass by aesop),
    (show Hilbert.S4Dot3.axioms = Hilbert.S4.axioms ∪ {Axioms.Dot3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.ReflexiveTransitiveFrameClass (Hilbert.S4.axioms) ConnectedFrameClass {Axioms.Dot3 (.atom 0) (.atom 1)};

instance : Kripke.ReflexiveTransitiveConnectedFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, Connected];


namespace Hilbert.S4Dot3

instance Kripke.sound : Sound (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := inferInstance

instance Kripke.consistent : System.Consistent (Hilbert.S4Dot3) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.ReflexiveTransitiveConnectedFrameClass


open
  Kripke
  MaximalConsistentSet
in
instance Kripke.canonical : Canonical (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := by
  have hS4 := canonicalFrame.multigeachean_of_provable_geach (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩}) (𝓢 := Hilbert.S4Dot3) (by simp);
  constructor;
  refine ⟨?_, ?_, ?_⟩;
  . simpa [reflexive_def] using @hS4 (⟨0, 0, 1, 0⟩) $ by tauto;
  . simpa [transitive_def] using @hS4 ⟨0, 2, 1, 0⟩ $ by tauto;
  . intro X Y Z ⟨hXY, hXZ⟩;
    by_contra hC;
    push_neg at hC;
    have ⟨hnYZ, hnZY⟩ := hC; clear hC;
    simp only [Set.not_subset] at hnYZ hnZY;
    obtain ⟨φ, hpY, hpZ⟩ := hnYZ; replace hpY : □φ ∈ Y := hpY;
    obtain ⟨ψ, hqZ, hqY⟩ := hnZY; replace hqZ : □ψ ∈ Z := hqZ;
    have hpqX : □(□φ ➝ ψ) ∉ X := by
      apply iff_mem_box.not.mpr;
      push_neg;
      use Y;
      constructor;
      . assumption;
      . apply iff_mem_imp.not.mpr;
        aesop;
    have hqpX : □(□ψ ➝ φ) ∉ X := by
      apply iff_mem_box.not.mpr; push_neg;
      use Z;
      constructor;
      . assumption;
      . apply iff_mem_imp.not.mpr;
        aesop;
    have : (□(□φ ➝ ψ) ⋎ □(□ψ ➝ φ)) ∉ X := by apply iff_mem_or.not.mpr; push_neg; exact ⟨hpqX, hqpX⟩;
    have : □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ) ∈ X := by
      apply membership_iff.mpr;
      exact System.axiomDot3!;
    contradiction;

instance Kripke.complete : Complete (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := inferInstance

end Hilbert.S4Dot3


end LO.Modal

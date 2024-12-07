import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal

namespace Kripke

abbrev ConnectedFrameClass : FrameClass := { F | Connected F }

abbrev ReflexiveTransitiveConnectedFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

open System
open Kripke
open Formula (atom)
open Formula.Kripke

variable {F : Kripke.Frame}

private lemma connected_of_dot3 : F ⊧* .𝟯 → Connected F := by
  contrapose;
  intro hCon; simp [Connected] at hCon;
  obtain ⟨x, y, Rxy, z, Ryz, nRyz, nRzy⟩ := hCon;
  simp [ValidOnFrame, ValidOnModel];
  use (atom 0), (atom 1),  (λ w a => match a with | 0 => y ≺ w | 1 => z ≺ w | _ => False), x;
  apply Satisfies.or_def.not.mpr;
  push_neg;
  constructor;
  . apply Satisfies.box_def.not.mpr; push_neg;
    use y;
    constructor;
    . assumption;
    . simp_all [Semantics.Realize, Satisfies];
  . apply Satisfies.box_def.not.mpr; push_neg;
    use z;
    constructor;
    . assumption;
    . simp_all [Semantics.Realize, Satisfies];

private lemma dot3_of_connected : Connected F → F ⊧* .𝟯 := by
  intro hCon;
  simp [ValidOnFrame, ValidOnModel, Axioms.Dot3];
  rintro _ φ ψ rfl V x;
  apply Satisfies.or_def.mpr;
  simp [Semantics.Realize, Satisfies];
  by_contra hC; push_neg at hC;
  obtain ⟨⟨y, rxy, hp, hnq⟩, ⟨z, rxz, hq, hnp⟩⟩ := hC;
  cases hCon ⟨rxy, rxz⟩ with
  | inl ryz => have := hp z ryz; contradiction;
  | inr rzy => have := hq y rzy; contradiction;

lemma ConnectedFrameClass.is_defined_by_Dot3 : ConnectedFrameClass.DefinedBy .𝟯 := by
  intro F;
  constructor;
  . apply dot3_of_connected;
  . apply connected_of_dot3;

lemma ReflexiveTransitiveConnectedFrameClass.is_defined_by_T_Four_Dot3 : ReflexiveTransitiveConnectedFrameClass.DefinedBy (𝗧 ∪ 𝟰 ∪ .𝟯) := by
  intro F;
  rw [Semantics.RealizeSet.union_iff, Semantics.RealizeSet.union_iff];
  constructor;
  . rintro ⟨hRef, hTrans, hConn⟩;
    refine ⟨⟨?_, ?_⟩, ?_⟩;
    . exact ReflexiveFrameClass.isDefinedBy F |>.mp hRef;
    . exact TransitiveFrameClass.isDefinedBy F |>.mp hTrans;
    . exact ConnectedFrameClass.is_defined_by_Dot3 F |>.mp hConn;
  . rintro ⟨⟨hT, h4⟩, hDot3⟩;
    refine ⟨?_, ?_, ?_⟩;
    . exact ReflexiveFrameClass.isDefinedBy F |>.mpr hT;
    . exact TransitiveFrameClass.isDefinedBy F |>.mpr h4;
    . exact ConnectedFrameClass.is_defined_by_Dot3 F |>.mpr hDot3;

end Kripke


namespace Hilbert

open Modal.Kripke
open Hilbert.Kripke

instance S4Dot3.Kripke.sound : Sound (Hilbert.S4Dot3 ℕ) (Kripke.ReflexiveTransitiveConnectedFrameClass)
  := instSound_of_frameClass_definedBy (Kripke.ReflexiveTransitiveConnectedFrameClass.is_defined_by_T_Four_Dot3) rfl

instance S4Dot3.consistent : System.Consistent (Hilbert.S4Dot3 ℕ) := instConsistent_of_nonempty_frameclass (C := Kripke.ReflexiveTransitiveConnectedFrameClass) $ by
  use reflexivePointFrame.toFrame;
  simp [Reflexive, Transitive, Connected];


open MaximalConsistentTheory in
lemma Kripke.canonicalFrame.is_connected_of_subset_Dot3
  (hAx : .𝟯 ⊆ Ax) [(Hilbert.ExtK Ax).Consistent] : Connected (canonicalFrame (Hilbert.ExtK Ax)) := by
  dsimp only [Connected];
  intro X Y Z ⟨hXY, hXZ⟩;
  by_contra hC; push_neg at hC;
  have ⟨nhYZ, nhZY⟩ := hC; clear hC;
  simp only [Set.not_subset] at nhYZ nhZY;
  obtain ⟨φ, hpY, hpZ⟩ := nhYZ; replace hpY : □φ ∈ Y.theory := hpY;
  obtain ⟨ψ, hqZ, hqY⟩ := nhZY; replace hqZ : □ψ ∈ Z.theory := hqZ;

  have hpqX : □(□φ ➝ ψ) ∉ X.theory := by
    apply iff_mem_box.not.mpr; push_neg;
    use Y;
    constructor;
    . assumption;
    . apply iff_mem_imp.not.mpr; simp [hpY, hqY];
  have hqpX : □(□ψ ➝ φ) ∉ X.theory := by
    apply iff_mem_box.not.mpr; push_neg;
    use Z;
    constructor;
    . assumption;
    . apply iff_mem_imp.not.mpr; simp [hpZ, hqZ];

  have : (□(□φ ➝ ψ) ⋎ □(□ψ ➝ φ)) ∉ X.theory := by apply iff_mem_or.not.mpr; push_neg; exact ⟨hpqX, hqpX⟩;
  have : □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ) ∈ X.theory := by apply subset_axiomset _; aesop;
  contradiction;

open Kripke.canonicalFrame

instance S4Dot3.complete : Complete (Hilbert.S4Dot3 ℕ) (Kripke.ReflexiveTransitiveConnectedFrameClass)
  := Kripke.instCompleteOfCanonical (C := Kripke.ReflexiveTransitiveConnectedFrameClass) $ by
  refine ⟨?reflexive, ?transitive, ?connective⟩;
  . apply is_reflexive_of_subset_T; simp;
  . apply is_transitive_of_subset_Four; simp;
  . apply is_connected_of_subset_Dot3; simp;

end Hilbert

end LO.Modal

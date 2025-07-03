import Foundation.Modal.Kripke.Cluster
import Foundation.Modal.Kripke.Terminated
import Foundation.Modal.Kripke.LinearFrame

namespace LO.Modal.Kripke

class Frame.IsBalloon (F : Frame) [F.IsTransitive] (e : Cluster F) extends IsStrictTotalOrder _ F, IsTerminated (F.strictSkelteon) e where
  envelope_non_degenerated : ¬e.degenerate
  not_envelope_degenerated : ∀ C, C ≠ e → C.degenerate

namespace Frame.IsBalloon

open Formula.Kripke

variable {F : Frame} [IsStrictTotalOrder _ F] {e : Cluster F} [F.IsBalloon e] {x : F.World} {φ : Formula ℕ}

/-- Every points in enverope is reflexive. -/
lemma rfl_in_envelope (hx : x ∈ e) : x ≺ x := Cluster.refl_of_mem_non_degenerate (envelope_non_degenerated) hx

/-- Every point in balloon can see all points in envelope. -/
lemma covered_in_envelope (x : F.World) : ∀ t ∈ e, x ≺ t := by
  obtain ⟨t₁, rfl⟩ := Quotient.exists_rep e;
  intro t₂ ht₂;
  replace ht₂ := Cluster.mem_iff₂.mp ht₂;
  rcases ht₂ with rfl | ⟨Rt₁₂, Rt₂₁⟩;
  . by_cases ext₁ : (⟦x⟧ : Cluster F) = ⟦t₁⟧;
    . simp only [Quotient.eq] at ext₁;
      rcases ext₁ with rfl | ⟨Rxt₁, Rtx₁⟩;
      . exact rfl_in_envelope (by tauto);
      . assumption;
    . have := IsTerminated.direct_terminated_of_trans (F := F.strictSkelteon) (t := ⟦t₁⟧) ⟦x⟧ ext₁;
      exact this.1;
  . by_cases ext₁ : (⟦x⟧ : Cluster F) = ⟦t₁⟧;
    . rcases Cluster.iff_eq_cluster.mp ext₁ with rfl | ⟨Rxt₁, Rtx₁⟩;
      . assumption;
      . exact _root_.trans Rxt₁ Rt₁₂;
    . have := IsTerminated.direct_terminated_of_trans (F := F.strictSkelteon) (t := ⟦t₁⟧) ⟦x⟧ ext₁;
      exact _root_.trans this.1 Rt₁₂;

/-- Every points from enverope is in enverope. -/
lemma in_envelope_of_in_envelope (hx : x ∈ e) : ∀ {y}, x ≺ y → y ∈ e := by
  obtain ⟨t, rfl⟩ := Quotient.exists_rep e;
  intro y Rxy;
  apply Cluster.mem_iff₂.mpr;
  by_cases t = y;
  . tauto;
  . right;
    replace hx := Cluster.mem_iff₂.mp hx;
    rcases hx with rfl | ⟨Rtx, Rxt⟩;
    . constructor;
      . exact Rxy;
      . apply covered_in_envelope (e := ⟦t⟧);
        tauto;
    . constructor;
      . exact _root_.trans Rtx Rxy;
      . apply covered_in_envelope (e := ⟦t⟧);
        tauto;

end Frame.IsBalloon

/-- In finite strict total ordered frame, `□φ` is not valid at x, farthest point from `x` exists s.t. not validate `φ` and validate `□φ`. -/
lemma farthermost_point_of_not_box {M : Kripke.Model} [IsStrictOrder _ M.toFrame] {x : M} (h : ¬x ⊧ □φ) : ∃ y, x ≺ y ∧ ¬y ⊧ φ ∧ y ⊧ □φ := by
  sorry;

open
  Formula.Kripke
  Frame.IsBalloon
in
lemma balooon_validates_axiomZ
  {F : Frame} [F.IsTransitive] {e : Cluster F} [F.IsBalloon e] : F ⊧ (Axioms.Z (.atom 0)) := by
  intro V x;
  suffices ¬(Satisfies _ x (□(□(.atom 0) ➝ (.atom 0)))) ∨ ¬(Satisfies _ x (◇□(.atom 0))) ∨ (Satisfies _ x (□(.atom 0))) by tauto;
  by_cases h : Satisfies _ x (□(.atom 0));
  . right; right; assumption;
  . obtain ⟨y, Rxy, hy, hy_far⟩ := farthermost_point_of_not_box h;
    by_cases hxT : x ∈ e;
    . right; left;
      apply Satisfies.dia_def.not.mpr;
      push_neg;
      intro z Rxz;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use y;
      constructor;
      . have hzT : z ∈ e := in_envelope_of_in_envelope hxT Rxz;
        rcases Cluster.mem_same_cluster hxT hzT with rfl | ⟨Rzx, Rxz⟩;
        . assumption;
        . exact _root_.trans Rzx Rxy;
      . assumption;
    . left;
      apply Satisfies.box_def.not.mpr;
      push_neg;
      use y;
      constructor;
      . assumption;
      . apply Satisfies.imp_def₂.not.mpr
        push_neg;
        tauto;

end LO.Modal.Kripke

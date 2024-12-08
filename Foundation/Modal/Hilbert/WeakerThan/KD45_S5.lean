import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KD45_weakerThan_S5 : (Hilbert.KD45 ℕ) ≤ₛ (Hilbert.S5 ℕ) :=  by
  apply Kripke.weakerThan_of_subset_FrameClass SerialTransitiveEuclideanFrameClass ReflexiveEuclideanFrameClass;
  rintro F ⟨F_refl, F_eucl⟩;
  refine ⟨serial_of_refl F_refl, trans_of_refl_eucl F_refl F_eucl, F_eucl⟩;

theorem KD45_strictlyWeakerThan_S5 : (Hilbert.KD45 ℕ) <ₛ (Hilbert.S5 ℕ) := by
  constructor;
  . exact KD45_weakerThan_S5;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply KD45.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Serial F.Rel ∧ Transitive F.Rel ∧ Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨Fin 2, λ x y => y = 1⟩;
      use F;
      refine ⟨?_, ?_, ?_, ?_⟩;
      . simp [Serial];
      . simp [Transitive];
      . simp [Euclidean];
      . use (λ w _ => w = 1), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

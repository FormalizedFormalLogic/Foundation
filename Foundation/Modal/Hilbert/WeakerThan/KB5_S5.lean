import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KB5_weakerThan_S5 : (Hilbert.KB5 ℕ) ≤ₛ (Hilbert.S5 ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass SymmetricEuclideanFrameClass ReflexiveEuclideanFrameClass;
  rintro F ⟨h_refl, h_eucl⟩;
  refine ⟨symm_of_refl_eucl h_refl h_eucl, h_eucl⟩;

theorem KB5_strictlyWeakerThan_S5 : (Hilbert.KB5 ℕ) <ₛ (Hilbert.S5 ℕ) := by
  constructor;
  . exact KB5_weakerThan_S5;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply KB5.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame,  Symmetric F.Rel ∧ Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      use ⟨Fin 1, λ x y => False⟩;
      refine ⟨?_, ?_, ?_⟩;
      . simp [Symmetric];
      . simp [Euclidean];
      . use (λ w _ => False), 0;
        simp [Satisfies, Semantics.Realize];

end LO.Modal.Hilbert

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K45_weakerThan_KB4 : (Hilbert.K45 ℕ) ≤ₛ (Hilbert.KB4 ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass TransitiveEuclideanFrameClass SymmetricTransitiveFrameClass;
  rintro F ⟨h_symm, h_trans⟩;
  refine ⟨h_trans, (eucl_of_symm_trans h_symm h_trans)⟩;

theorem K45_strictlyWeakerThan_KB4 : (Hilbert.K45 ℕ) <ₛ (Hilbert.KB4 ℕ) := by
  constructor;
  . exact K45_weakerThan_KB4;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply K45.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame,  Transitive F.Rel ∧ Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      use ⟨Fin 2, λ x y => y = 1⟩;
      refine ⟨?_, ?_, ?_⟩;
      . simp [Transitive];
      . simp [Euclidean];
      . use (λ w _ => w = 0), 0;
        simp [Satisfies, Semantics.Realize];

end LO.Modal.Hilbert

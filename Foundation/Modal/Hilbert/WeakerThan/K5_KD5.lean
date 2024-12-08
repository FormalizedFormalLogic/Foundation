import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K5_weakerThan_KD5 : (Hilbert.K5 α) ≤ₛ (Hilbert.KD5 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem K5_strictlyWeakerThan_KD5 : (Hilbert.K5 ℕ) <ₛ (Hilbert.KD5 ℕ) := by
  constructor;
  . exact K5_weakerThan_KD5;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ ◇(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply K5.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨Fin 1, λ x y => False⟩;
      use F;
      constructor;
      . simp [Euclidean];
      . use (λ w _ => w = 0), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

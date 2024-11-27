import Foundation.Modal.Kripke.Geach

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K4_weakerThan_S4 : (Hilbert.K4 α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem K4_strictlyWeakerThan_S4 : (Hilbert.K4 ℕ) <ₛ (Hilbert.S4 ℕ) := by
  constructor;
  . exact K4_weakerThan_S4;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! (by simp)
    . apply K4.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 3, λ _ y => y = 1⟩;
      constructor;
      . intro _ _ _; simp_all;
      . use (λ w _ => w = 1), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

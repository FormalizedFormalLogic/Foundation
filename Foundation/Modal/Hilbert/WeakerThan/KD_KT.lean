import Foundation.Modal.Kripke.Geach

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula (atom)
open Formula.Kripke

lemma KD_weakerThan_KT : (Hilbert.KD ℕ) ≤ₛ (Hilbert.KT ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass SerialFrameClass ReflexiveFrameClass;
  intro F hF; apply serial_of_refl hF;

theorem KD_strictlyWeakerThan_KT : (Hilbert.KD ℕ) <ₛ (Hilbert.KT ℕ) := by
  constructor;
  . exact KD_weakerThan_KT;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KD.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ _ y => y = 1⟩;
      constructor;
      . intro x; use 1;
      . use (λ w _ => w = 1), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

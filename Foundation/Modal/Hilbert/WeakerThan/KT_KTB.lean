import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula (atom)
open Formula.Kripke

lemma KT_weakerThan_KTB : (Hilbert.KT α) ≤ₛ (Hilbert.KTB α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KT_strictlyWeakerThan_KTB : (Hilbert.KT ℕ) <ₛ (Hilbert.KTB ℕ) := by
  constructor;
  . exact KT_weakerThan_KTB;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KT.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x ≤ y⟩;
      constructor;
      . simp [Reflexive];
      . use (λ x _ => x = 0), 0;
        simp [Semantics.Realize, Satisfies];
        use 1;
        omega;

end LO.Modal.Hilbert

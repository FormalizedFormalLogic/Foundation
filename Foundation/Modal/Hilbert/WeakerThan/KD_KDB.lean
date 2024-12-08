import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KD_weakerThan_KDB : (Hilbert.KD α) ≤ₛ (Hilbert.KDB α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KD_strictlyWeakerThan_KDB : (Hilbert.KD ℕ) <ₛ (Hilbert.KDB ℕ) := by
  constructor;
  . exact KD_weakerThan_KDB;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KD.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Serial F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Satisfies ⟨F, V⟩ w _)  by
        simpa [ValidOnModel, ValidOnFrame, Satisfies];
      let F : Frame := ⟨Fin 2, λ x y => x ≤ y⟩;
      use F;
      constructor;
      . intro x;
        match x with
        | 0 => use 1; omega;
        | 1 => use 1;
      . use (λ w _ => w = 0), 0;
        suffices ∃ x, (0 : F.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies];
        use 1;
        omega;

end LO.Modal.Hilbert

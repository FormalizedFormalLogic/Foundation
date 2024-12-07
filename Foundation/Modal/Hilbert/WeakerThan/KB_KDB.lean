import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KB_weakerThan_KDB : (Hilbert.KB α) ≤ₛ (Hilbert.KDB α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KB_strictlyWeakerThan_KDB : (Hilbert.KB ℕ) <ₛ (Hilbert.KDB ℕ) := by
  constructor;
  . exact KB_weakerThan_KDB;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ ◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KB.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Symmetric F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Satisfies ⟨F, V⟩ w _)  by
        simpa [ValidOnModel, ValidOnFrame, Satisfies];
      let F : Frame := ⟨Fin 1, λ x y => False⟩;
      use F;
      constructor;
      . simp [Symmetric];
      . use (λ w _ => w = 0), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

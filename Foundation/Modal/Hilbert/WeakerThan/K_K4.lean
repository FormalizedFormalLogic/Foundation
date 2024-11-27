import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Hilbert

open System
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_K4 : (Hilbert.K ℕ) <ₛ (Hilbert.K4 ℕ) := by
  constructor;
  . simp;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ □□(atom 0));
    constructor;
    . exact axiomFour!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x ≠ y⟩, (λ w _ => w = 1), 0;
      simp [Semantics.Realize, Satisfies];
      constructor;
      . intro x;
        match x with
        | 0 => tauto;
        | 1 => tauto;
      . use 1;
        constructor;
        . tauto;
        . use 0; tauto;

end LO.Modal.Hilbert

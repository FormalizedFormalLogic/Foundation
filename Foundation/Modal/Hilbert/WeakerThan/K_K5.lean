import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Hilbert

open System
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_K5 : (Hilbert.K ℕ) <ₛ (Hilbert.K5 ℕ) := by
  constructor;
  . simp;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (◇(atom default) ➝ □◇(atom default));
    constructor;
    . exact axiomFive!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x _ => x = 0⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];
      use 1;
      tauto;

end LO.Modal.Hilbert

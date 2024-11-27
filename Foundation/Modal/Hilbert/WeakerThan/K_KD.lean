import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Hilbert

open System
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_KD : (Hilbert.K ℕ) <ₛ (Hilbert.KD ℕ) := by
  constructor;
  . simp;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ ◇(atom 0));
    constructor;
    . exact axiomD!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 1, λ _ _ => False⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

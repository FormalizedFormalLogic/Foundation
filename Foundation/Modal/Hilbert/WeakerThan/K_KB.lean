import Foundation.Modal.Kripke.Basic

namespace LO.Modal.Hilbert

open System
open Formula (atom)
open Formula.Kripke

theorem K_strictlyWeakerThan_KB : (Hilbert.K ℕ) <ₛ (Hilbert.KB ℕ) := by
  constructor;
  . simp;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use ((atom 0) ➝ □◇(atom 0));
    constructor;
    . exact axiomB!;
    . apply K.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 2, λ x y => x = 0 ∧ y = 1⟩, (λ w _ => w = 0), 0;
      simp [Semantics.Realize, Satisfies];
      use 1;
      tauto;

end LO.Modal.Hilbert

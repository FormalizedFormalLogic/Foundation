import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K4_weakerThan_K45 : (Hilbert.K4 α) ≤ₛ (Hilbert.K45 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem K4_strictlyWeakerThan_K45 : (Hilbert.K4 ℕ) <ₛ (Hilbert.K45 ℕ) := by
  constructor;
  . exact K4_weakerThan_K45;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (◇(atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply K4.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Transitive F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨Fin 2, λ x y => x < y⟩;
      use F;
      constructor;
      . simp [Transitive];
        omega;
      . use (λ w _ => w = 1), 0;
        suffices (0 : F.World) ≺ 1 ∧ ∃ x : F.World, (0 : F.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1; omega;

end LO.Modal.Hilbert

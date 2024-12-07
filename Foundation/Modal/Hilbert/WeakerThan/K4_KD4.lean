import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K4_weakerThan_KD4 : (Hilbert.K4 α) ≤ₛ (Hilbert.KD4 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem K4_strictlyWeakerThan_KD4 : (Hilbert.K4 ℕ) <ₛ (Hilbert.KD4 ℕ) := by
  constructor;
  . exact K4_weakerThan_KD4;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ ◇(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply K4.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Transitive F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨Fin 1, λ x y => False⟩;
      use F;
      constructor;
      . simp [Transitive];
      . use (λ w _ => w = 0), 0;
        simp [Semantics.Realize, Satisfies];

end LO.Modal.Hilbert

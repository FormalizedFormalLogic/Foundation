import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KD4_weakerThan_KD45 : (Hilbert.KD4 α) ≤ₛ (Hilbert.KD45 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KD4_strictlyWeakerThan_KD45 : (Hilbert.KD4 ℕ) <ₛ (Hilbert.KD45 ℕ) := by
  constructor;
  . exact KD4_weakerThan_KD45;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (◇(atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply KD4.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Serial F.Rel ∧ Transitive F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨Fin 2, λ x y => x = y ∨ x < y⟩;
      use F;
      refine ⟨?_, ?_, ?_⟩;
      . unfold Serial;
        aesop;
      . unfold Transitive;
        omega;
      . use (λ w _ => w = 0), 0;
        suffices (0 : F.World) ≺ 0 ∧ ∃ x : F.World, (0 : F.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1; omega;

end LO.Modal.Hilbert

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KD5_weakerThan_KD45 : (Hilbert.KD5 α) ≤ₛ (Hilbert.KD45 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KD5_strictlyWeakerThan_KD45 : (Hilbert.KD5 ℕ) <ₛ (Hilbert.KD45 ℕ) := by
  constructor;
  . exact KD5_weakerThan_KD45;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ □□(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply KD5.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Serial F.Rel ∧ Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨
        Fin 3,
        λ x y =>
          match x, y with
          | 0, 1 => True
          | 1, 2 => True
          | 1, 1 => True
          | 2, 1 => True
          | 2, 2 => True
          | _, _ => False
      ⟩;
      use F;
      refine ⟨?_, ?_, ?_⟩;
      . intro x;
        match x with
        | 0 => use 1; tauto;
        | 1 => use 2; tauto;
        | 2 => use 1; tauto;
      . unfold Euclidean; aesop;
      . use (λ w _ => w = 1), 0;
        suffices (∀ (y : F.World), (0 : F.World) ≺ y → y = 1) ∧ ∃ x, (0 : F.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro y;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            constructor;
            . tauto;
            . simp;

end LO.Modal.Hilbert

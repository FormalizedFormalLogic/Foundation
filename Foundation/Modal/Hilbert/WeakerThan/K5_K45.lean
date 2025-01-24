import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma K5_weakerThan_K45 : (Hilbert.K5 α) ≤ₛ (Hilbert.K45 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem K5_strictlyWeakerThan_K45 : (Hilbert.K5 ℕ) <ₛ (Hilbert.K45 ℕ) := by
  constructor;
  . exact K5_weakerThan_K45;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ □□(atom 0));
    constructor;
    . exact Deduction.maxm! $ by simp;
    . apply K5.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Euclidean F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Kripke.Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨
          Fin 3,
          λ x y =>
            match x, y with
            | 0, 1 => True
            | 1, 1 => True
            | 1, 2 => True
            | 2, 1 => True
            | 2, 2 => True
            | _, _ => False
        ⟩;
      use F;
      constructor;
      . unfold Euclidean; aesop;
      . use (λ w _ => w = 1), 0;
        suffices (∀ (y : F.World), (0 : F.World) ≺ y → y = 1) ∧ ∃ x, (0 : F.World) ≺ x ∧ ∃ z, x ≺ z ∧ ¬z = 1 by simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro y R0y;
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
            . trivial;

end LO.Modal.Hilbert

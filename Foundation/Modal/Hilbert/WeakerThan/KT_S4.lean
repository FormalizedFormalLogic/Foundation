import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KT_weakerThan_S4 : (Hilbert.KT α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

theorem KT_strictlyWeakerThan_S4 : (Hilbert.KT ℕ) <ₛ (Hilbert.S4 ℕ) := by
  constructor;
  . exact KT_weakerThan_S4;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ □□(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KT.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Reflexive F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Satisfies ⟨F, V⟩ w _)  by
        simpa [ValidOnModel, ValidOnFrame, Satisfies];
      let F : Frame := ⟨
        Fin 3,
        λ x y =>
          match x, y with
          | 0, 0 => True
          | 0, 1 => True
          | 1, 1 => True
          | 1, 2 => True
          | 2, 2 => True
          | _, _ => False
      ⟩;
      use F;
      constructor;
      . intro x;
        match x with
        | 0 => tauto;
        | 1 => tauto;
        | 2 => tauto;
      . use (λ w _ => w = 0 ∨ w = 1), 0;
        suffices (∀ (y : F.World), (0 : F.World) ≺ y → y = 0 ∨ y = 1) ∧ ∃ x, (0 : F.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 0 ∧ y ≠ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . intro y hy;
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

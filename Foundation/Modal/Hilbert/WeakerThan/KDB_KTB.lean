import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KDB_weakerThan_KTB : (Hilbert.KDB ℕ) ≤ₛ (Hilbert.KTB ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass SerialSymmetricFrameClass ReflexiveSymmetricFrameClass;
  rintro F ⟨F_refl, F_symm⟩;
  refine ⟨serial_of_refl F_refl, F_symm⟩;

theorem KDB_strictlyWeakerThan_KTB : (Hilbert.KDB ℕ) <ₛ (Hilbert.KTB ℕ) := by
  constructor;
  . exact KDB_weakerThan_KTB;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (□(atom 0) ➝ (atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KDB.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Serial F.Rel ∧ Symmetric F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Satisfies ⟨F, V⟩ w _)  by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      use ⟨Fin 2, λ x y => x ≠ y⟩;
      refine ⟨?_, ?_, ?_⟩;
      . intro x;
        match x with
        | 0 => use 1; simp;
        | 1 => use 0; simp;
      . unfold Symmetric;
        tauto;
      . use (λ x _ => x = 1), 0;
        simp [Semantics.Realize, Satisfies];
        omega;

end LO.Modal.Hilbert

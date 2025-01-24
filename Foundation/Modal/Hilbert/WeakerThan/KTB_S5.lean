import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma KTB_weakerThan_S5 : (Hilbert.KTB ℕ) ≤ₛ (Hilbert.S5 ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass ReflexiveSymmetricFrameClass ReflexiveEuclideanFrameClass;
  rintro F ⟨F_refl, F_eucl⟩;
  refine ⟨F_refl, symm_of_refl_eucl F_refl F_eucl⟩;

theorem KTB_strictlyWeakerThan_S5 : (Hilbert.KTB ℕ) <ₛ (Hilbert.S5 ℕ) := by
  constructor;
  . exact KTB_weakerThan_S5;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (◇(atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply KTB.Kripke.sound.not_provable_of_countermodel;
      suffices ∃ F : Frame, Reflexive F.Rel ∧ Symmetric F.Rel ∧ ∃ V : Valuation F, ∃ w : F.World, ¬(Satisfies ⟨F, V⟩ w _) by
        simp [ValidOnModel, ValidOnFrame, Satisfies];
        tauto;
      let F : Frame := ⟨
        Fin 3,
        λ x y =>
          match x, y with
          | 1, 2 => False
          | 2, 1 => False
          | _, _ => True
      ⟩;
      use F;
      refine ⟨?_, ?_, ?_⟩;
      . unfold Reflexive;
        aesop;
      . unfold Symmetric;
        aesop;
      . use (λ w _ => w = 1), 0;
        suffices (0 : F.World) ≺ 1 ∧ ∃ x, (0 : F.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 2;
          tauto;

end LO.Modal.Hilbert

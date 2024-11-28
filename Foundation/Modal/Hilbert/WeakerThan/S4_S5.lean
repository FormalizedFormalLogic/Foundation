import Foundation.Modal.Kripke.Geach

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

lemma S4_weakerThan_S5 : (Hilbert.S4 ℕ) ≤ₛ (Hilbert.S5 ℕ) := by
  apply Kripke.weakerThan_of_subset_FrameClass ReflexiveTransitiveFrameClass ReflexiveEuclideanFrameClass;
  rintro _ ⟨F_refl, F_eucl⟩;
  refine ⟨F_refl, trans_of_refl_eucl F_refl F_eucl⟩;

theorem S4_strictlyWeakerThan_S5 : (Hilbert.S4 ℕ) <ₛ (Hilbert.S5 ℕ) := by
  constructor;
  . exact S4_weakerThan_S5;
  . apply weakerThan_iff.not.mpr;
    push_neg;
    use (◇(atom 0) ➝ □◇(atom 0));
    constructor;
    . exact Deduction.maxm! (by simp);
    . apply S4.Kripke.sound.not_provable_of_countermodel;
      simp [ValidOnModel, ValidOnFrame, Satisfies];
      use ⟨Fin 3, λ x y => (x = y) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩;
      refine ⟨?_, ?_, ?_⟩;
      . simp [Reflexive];
      . simp [Transitive];
        omega;
      . use (λ w _ => w = 2), 0;
        simp [Satisfies, Semantics.Realize];
        constructor;
        . omega;
        . use 1; omega;

end LO.Modal.Hilbert

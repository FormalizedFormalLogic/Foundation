import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Hilbert.WellKnown


namespace Set

variable {s t : Set α}

abbrev Cofinite (s : Set α) := sᶜ.Finite

@[simp]
lemma cofinite_compl : sᶜ.Cofinite ↔ s.Finite := by simp [Set.Cofinite];

lemma comp_finite : s.Finite → sᶜ.Cofinite := cofinite_compl.mpr

end Set


namespace LO.Modal

open System
open Kripke
open Formula
open Formula.Kripke

namespace Kripke

variable {F : Kripke.Frame} {a : ℕ}

lemma valid_atomic_H_of_valid_atomic_L : F ⊧ (Axioms.L (atom a)) → F ⊧ (Axioms.H (atom a)) := by
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (□(□a ➝ a)) := by
    intro y Rxy;
    exact (Satisfies.and_def.mp $ @hx y Rxy) |>.1;
  exact @h V x this;

lemma valid_atomic_L_of_valid_atomic_H : F ⊧ Axioms.H (atom a) → F ⊧ Axioms.L (atom a) := by
  intro hH V x hx;

  let V' : Valuation F := λ w a => ∀ n : ℕ, Satisfies ⟨F, V⟩ w (□^[n] a);

  have h₁ : Satisfies ⟨F, V'⟩ x (□(□a ⭤ a)) := by
    intro y Rxy;
    have : Satisfies ⟨F, V'⟩ y a ↔ Satisfies ⟨F, V'⟩ y (□a) := calc
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[n] a) := by simp [Satisfies, V'];
      _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (□^[(n + 1)]a) := by
        constructor;
        . intro h n; apply h;
        . intro h n;
          have h₁ : Satisfies ⟨F, V⟩ y (□□^[n](atom a) ➝ □^[n](atom a)) := by
            induction n with
            | zero => apply @hx y Rxy;
            | succ n => intro _; apply h;
          apply h₁;
          simpa using h n;
      _ ↔ ∀ n, ∀ z, y ≺ z → Satisfies ⟨F, V⟩ z (□^[n] a) := by simp [Satisfies];
      _ ↔ ∀ z, y ≺ z → ∀ n : ℕ, Satisfies ⟨F, V⟩ z (□^[n]a) := by aesop;
      _ ↔ ∀ z, y ≺ z → Satisfies ⟨F, V'⟩ z (atom a) := by simp [Satisfies, V'];
      _ ↔ Satisfies ⟨F, V'⟩ y (□(atom a)) := by simp [Satisfies];
    simp [Satisfies, V'];
    tauto;

  have h₂ : Satisfies ⟨F, V'⟩ x (□atom a) := @hH V' x h₁;

  intro w Rxw;
  exact @h₂ w Rxw 0;

lemma valid_atomic_L_iff_valid_atomic_H : F ⊧ Axioms.L (atom 0) ↔ F ⊧ Axioms.H (atom 0) := by
  constructor;
  . exact valid_atomic_H_of_valid_atomic_L;
  . exact valid_atomic_L_of_valid_atomic_H;

lemma valid_atomic_4_of_valid_atomic_L : F ⊧ Axioms.L (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  intro h V x h₂ y Rxy z Ryz;
  refine h₂ z ?_;
  apply @trans_of_validate_L F h x y z Rxy Ryz;

lemma valid_atomic_Four_of_valid_atomic_H : F ⊧ Axioms.H (atom 0) → F ⊧ Axioms.Four (atom 0) := by
  trans;
  . exact valid_atomic_L_iff_valid_atomic_H.mpr;
  . exact valid_atomic_4_of_valid_atomic_L;

abbrev cresswellFrame : Kripke.Frame where
  World := ℕ × Fin 2
  Rel n m :=
    match n, m with
    | (n, 0), (m, 0) => n < m
    | (n, 1), (m, 1) => n ≤ m + 1
    | (_, 0), (_, 1) => True
    | _, _ => False

namespace cresswellFrame

abbrev Sharp := { w : cresswellFrame.World // w.2 = 0 }
@[match_pattern] abbrev sharp (n : ℕ) : Sharp := ⟨(n, 0), rfl⟩
postfix:max "♯" => sharp

abbrev Flat := { w : cresswellFrame.World // w.2 = 1 }
@[match_pattern] abbrev flat (n : ℕ) : Flat := ⟨(n, 1), rfl⟩
postfix:max "♭" => flat

end cresswellFrame


abbrev cresswellModel : Kripke.Model := ⟨cresswellFrame, λ w _ => w ≠ 0♭⟩

lemma not_valid_axiomFour_in_cresswellModel : ¬(Satisfies cresswellModel 2♭ (Axioms.Four (atom 0))) := by
  apply Satisfies.imp_def.not.mpr;
  push_neg;
  constructor;
  . intro x;
    match x with
    | (_, 0) => simp;
    | (_, 1) => simp [Satisfies]; omega;
  . apply Satisfies.box_def.not.mpr
    push_neg;
    use 1♭;
    constructor;
    . omega;
    . apply Satisfies.box_def.not.mpr;
      push_neg;
      use 0♭;
      constructor;
      . omega;
      . tauto;

lemma valid_axiomH_in_cresswellModel : cresswellModel ⊧ □(□φ ⭤ φ) ➝ □φ := by
  sorry;

lemma provable_KH_of_valid_cresswellModel : Hilbert.KH ⊢! φ → cresswellModel ⊧ φ := by
  intro h;
  induction h using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact Kripke.ValidOnModel.axiomK;
    . exact valid_axiomH_in_cresswellModel;
  | mdp ihφψ ihφ => exact Kripke.ValidOnModel.mdp ihφψ ihφ;
  | nec ihφ => exact Kripke.ValidOnModel.nec ihφ;
  | imply₁ => exact Kripke.ValidOnModel.imply₁;
  | imply₂ => exact Kripke.ValidOnModel.imply₂;
  | ec => exact Kripke.ValidOnModel.elimContra;

lemma KH_unprov_axiomFour : Hilbert.KH ⊬ Axioms.Four (atom 0) := fun hC =>
  not_valid_axiomFour_in_cresswellModel (provable_KH_of_valid_cresswellModel hC ↑2♭)

theorem KH_KripkeIncomplete : ¬∃ C : Kripke.FrameClass, ∀ φ, (Hilbert.KH ⊢! φ ↔ C ⊧ φ) := by
  rintro ⟨C, h⟩;
  have : C ⊧ Axioms.H (atom 0) := @h (Axioms.H (atom 0)) |>.mp $ by simp;
  have : C ⊧ Axioms.Four (atom 0) := fun {F} hF => valid_atomic_Four_of_valid_atomic_H (this hF);
  have : Hilbert.KH ⊢! Axioms.Four (atom 0) := @h (Axioms.Four (atom 0)) |>.mpr this;
  exact @KH_unprov_axiomFour this;

end Kripke

end LO.Modal

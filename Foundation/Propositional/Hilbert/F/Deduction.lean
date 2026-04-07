module

public import Foundation.Propositional.Hilbert.F.Basic

@[expose] public section

namespace LO.Propositional.Hilbert.F

open Entailment.Corsi

attribute [grind <=] Entailment.mdp!

variable {α : Type*} {H : HilbertF α} {Γ : Set (Formula α)} {φ ψ : Formula α}

inductive Deduction (H : HilbertF α) (Γ : Set (Formula α)) : Formula α → Prop
| protected ctx {φ}     : φ ∈ Γ → Deduction H Γ φ
| protected thm {φ}     : H ⊢ φ → Deduction H Γ φ
| protected mp {φ ψ}    : H ⊢ (φ 🡒 ψ) → Deduction H Γ φ → Deduction H Γ ψ
| protected andIR {φ ψ} : Deduction H Γ φ → Deduction H Γ ψ → Deduction H Γ (φ ⋏ ψ)

@[grind ⇒] lemma deducible_of_provable (hφ : H ⊢ φ) : Deduction H Γ φ := by apply Deduction.thm hφ;

@[simp, grind =]
lemma deducible_empty : Deduction H ∅ φ ↔ H ⊢ φ := by
  constructor;
  . intro h; induction h <;> grind;
  . grind;

@[grind ⇒]
lemma deduction_subset (h : Γ₁ ⊆ Γ₂) : Deduction H Γ₁ φ → Deduction H Γ₂ φ := by
  intro h;
  induction h with
  | ctx hφ => apply Deduction.ctx; grind;
  | thm hφ => apply Deduction.thm; assumption;
  | mp => apply Deduction.mp <;> assumption;
  | andIR => apply Deduction.andIR <;> assumption;

theorem WeakDT : (Deduction H {ψ} φ) ↔ H ⊢ ψ 🡒 φ := by
  constructor;
  . intro h; induction h <;> grind;
  . intro h;
    apply Deduction.mp h;
    apply Deduction.ctx;
    simp;

variable [DecidableEq α]

lemma deduct_conj {Γ : List (Formula α)} : Deduction H (Γ.toFinset) Γ.conj₂ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply Deduction.thm; simp;
  | hsingle φ => apply Deduction.ctx; simp;
  | hcons φ Γ hΓ ih =>
    rw [List.conj₂_cons_nonempty hΓ];
    apply Deduction.andIR;
    . apply Deduction.ctx; simp;
    . apply deduction_subset (Γ₁ := Γ.toFinset);
      . simp;
      . exact ih;

lemma DT_list {Γ : List (Formula α)} : (Deduction H Γ.toFinset φ) ↔ H ⊢ Γ.conj₂ 🡒 φ := by
  constructor;
  . intro h;
    induction h with
    | ctx hφ => sorry;
    | thm hφ => apply af hφ;
    | mp => grind;
    | andIR => apply CK_of_C_of_C <;> assumption;
  . intro h;
    induction Γ using List.induction_with_singleton with
    | hnil =>
      apply Deduction.mp h;
      apply Deduction.thm;
      exact Entailment.verum!;
    | hsingle =>
      apply Deduction.mp h;
      apply Deduction.ctx;
      simp;
    | hcons ψ Γ hΓ ih =>
      sorry;

lemma DT_finset {Γ : Finset (Formula α)} : (Deduction H Γ φ) ↔ (H ⊢ Γ.conj 🡒 φ) := by simpa using DT_list (Γ := Γ.toList);

lemma DT_set {Γ : Set (Formula α)} : (Deduction H Γ φ) ↔ ∃ Δ : Finset (Formula α), ↑Δ ⊆ Γ ∧ Deduction H Δ φ := by
  constructor;
  . intro h;
    induction h with
    | @ctx φ hφ =>
      use {φ};
      constructor;
      . grind;
      . apply Deduction.ctx;
        simp;
    | thm hφ => use ∅; grind;
    | mp hφψ _ ihφ =>
      obtain ⟨Δ, hΔ, hΔφ⟩ := ihφ;
      use Δ;
      constructor;
      . assumption;
      . exact Deduction.mp hφψ hΔφ;
    | andIR hΓφ hΓψ ihφ ihψ =>
      obtain ⟨Δ₁, hΔ₁, hΔ₁φ⟩ := ihφ;
      obtain ⟨Δ₂, hΔ₂, hΔ₂ψ⟩ := ihψ;
      use Δ₁ ∪ Δ₂;
      constructor;
      . grind;
      . apply Deduction.andIR;
        . apply deduction_subset (by grind) hΔ₁φ;
        . apply deduction_subset (by grind) hΔ₂ψ;
  . rintro ⟨Δ, hΔΓ, hφ⟩;
    apply deduction_subset hΔΓ hφ;

end LO.Propositional.Hilbert.F
end

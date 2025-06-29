import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K
import Foundation.Logic.HilbertStyle.Lukasiewicz
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {α : Type*}

structure Hilbert (α : Type*) where
  axioms : Set (Formula α)


namespace Hilbert

variable {H H₁ H₂ : Hilbert α}

abbrev axiomInstances (H : Hilbert α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;


inductive Deduction (H : Hilbert α) : (Formula α) → Prop
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

def Deduction.maxm' {H : Hilbert α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  apply Deduction.maxm;
  exact mem_axiomInstances_of_mem_axioms h;

def Deduction.subst {φ} (s) (h : Deduction H φ) : Deduction H (φ⟦s⟧) := by
  induction h with
  | imply₁ => apply Deduction.imply₁;
  | imply₂ => apply Deduction.imply₂;
  | ec => apply Deduction.ec;
  | mdp _ _ ihφψ ihφ => apply Deduction.mdp ihφψ ihφ;
  | nec _ ihφ => apply Deduction.nec; exact ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply Deduction.maxm;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;


abbrev logic (H : Hilbert α) : Logic α := H.Deduction

section

variable {H H₁ H₂ : Hilbert α} {φ ψ : Formula α}

lemma iff_mem_logic : H.logic ⊢! φ ↔ Deduction H φ := by simp [logic]; rfl;

instance : Entailment.Lukasiewicz (H.logic) where
  mdp hφψ hφ := by
    constructor;
    apply Deduction.mdp;
    . exact PLift.down hφψ;
    . exact PLift.down hφ;
  imply₁ _ _ := by constructor; apply Deduction.imply₁;
  imply₂ _ _ _ := by constructor; apply Deduction.imply₂;
  elimContra _ _ := by constructor; apply Deduction.ec;

instance : Entailment.Cl (H.logic) where

instance : Entailment.HasDiaDuality H.logic := inferInstance

instance : Entailment.Necessitation H.logic where
  nec hφ := by
    constructor;
    apply Deduction.nec;
    exact PLift.down hφ

instance : H.logic.Substitution where
  subst s hφ := by
    constructor;
    apply Deduction.subst;
    exact PLift.down hφ

lemma maxm! (h : φ ∈ H.axiomInstances) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm h;

lemma maxm'! (h : φ ∈ H.axioms) : H.logic ⊢! φ := by
  apply iff_mem_logic.mpr;
  exact Deduction.maxm' h;

@[induction_eliminator]
protected lemma rec!
  {motive     : (φ : Formula α) → (H.logic ⊢! φ) → Sort}
  (maxm       : ∀ {φ : Formula α}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ : Formula α}, {hpq : H.logic ⊢! φ ➝ ψ} → {hp : H.logic ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ : Formula α}, {hp : H.logic ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (imply₁     : ∀ {φ ψ : Formula α}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂     : ∀ {φ ψ χ : Formula α}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec         : ∀ {φ ψ : Formula α}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H.logic ⊢! φ) → motive φ d := by
  rintro φ d;
  induction iff_mem_logic.mp d with
  | maxm h =>
    apply maxm h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ $ iff_mem_logic.mpr hφψ;
    . exact ihφ $ iff_mem_logic.mpr hφ;
  | nec hφ ihφ =>
    apply nec;
    exact ihφ $ iff_mem_logic.mpr hφ;
  | imply₁ => apply imply₁;
  | imply₂ => apply imply₂;
  | ec => apply ec;

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr;
  intro _ h;
  induction h with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply H₂.logic.subst! s;
    exact maxm'! $ hs h;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | nec ih => exact nec! ih;
  | _ => simp;

lemma weakerThan_of_provable_axiomInstances (hs : H₂.logic ⊢!* H₁.axiomInstances) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr;
  intro _ h;
  induction h with
  | maxm h => exact hs h;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂
  | nec ih => exact nec! ih;
  | _ => simp;

lemma weakerThan_of_provable_axioms (hs : H₂.logic ⊢!* H₁.axioms) : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_of_provable_axiomInstances;
  rintro φ ⟨ψ, h, ⟨s, rfl⟩⟩;
  exact H₂.logic.subst! s (hs h);

end

end Hilbert

end LO.Modal

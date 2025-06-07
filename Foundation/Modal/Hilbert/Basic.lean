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

class FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms := by aesop


inductive Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}      : φ ∈ H.axiomInstances → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

namespace Deduction

instance : Entailment (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : Entailment.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elimContra := ec

instance : Entailment.Cl H where

instance : Entailment.HasDiaDuality H := inferInstance

instance : Entailment.Necessitation H := ⟨nec⟩

lemma maxm! {φ} (h : φ ∈ H.axiomInstances) : H ⊢! φ := ⟨maxm h⟩

end Deduction


open Deduction

namespace Deduction

noncomputable def rec!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (maxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ (maxm! h))
  (mdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (nec        : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (imply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (imply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
  (ec : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact maxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact nec (ih ⟨hp⟩)
  | _ => aesop;

def subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := by
  induction h using Deduction.rec! with
  | imply₁ => simp;
  | imply₂ => simp;
  | ec => simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | nec ihφ => exact nec! ihφ;
  | maxm h =>
    obtain ⟨ψ, h, ⟨s', rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . assumption;
    . use s' ∘ s;
      simp;

end Deduction

lemma of_subset (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⊢! φ → H₂ ⊢! φ := by
  intro h;
  induction h using Deduction.rec! with
  | maxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    apply maxm!;
    use ψ;
    constructor;
    . exact hs h;
    . use s;
  | mdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | nec ih => exact nec! ih;
  | _ => simp;

lemma weakerThan_of_dominate_axiomInstances (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axiomInstances → H₂ ⊢! φ) : H₁ ⪯ H₂ := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.rec! with
  | maxm h => apply hMaxm h;
  | mdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | nec ih => exact nec! ih;
  | _ => simp;

lemma weakerThan_of_dominate_axioms (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ) : H₁ ⪯ H₂ := by
  apply weakerThan_of_dominate_axiomInstances;
  rintro φ ⟨ψ, hψ, ⟨s, rfl⟩⟩;
  apply subst!;
  apply hMaxm hψ;


abbrev logic (H : Hilbert ℕ) : Logic := Entailment.theory H

section

variable {H : Hilbert ℕ}

@[simp]
lemma iff_mem_logic {φ : Formula ℕ} : φ ∈ H.logic ↔ H ⊢! φ := by simp [Entailment.theory];

instance [Entailment.Consistent H] : H.logic.Consistent := ⟨by
  apply Set.eq_univ_iff_forall.not.mpr;
  push_neg;
  obtain ⟨φ, hφ⟩ : ∃ φ, H ⊬ φ := Entailment.Consistent.exists_unprovable inferInstance;
  use! φ;
  simpa;
⟩

instance [Entailment.Unnecessitation H] : H.logic.Unnecessitation := ⟨fun {_} h => unnec! h⟩

instance [Entailment.ModalDisjunctive H] : H.logic.ModalDisjunctive := ⟨fun {_ _} h => modal_disjunctive h⟩

end

end Hilbert

end LO.Modal

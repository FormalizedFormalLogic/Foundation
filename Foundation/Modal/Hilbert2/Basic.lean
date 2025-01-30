import Foundation.Modal.Formula
import Foundation.Modal.Substitution
import Foundation.Modal.System.K
import Foundation.Logic.HilbertStyle.Lukasiewicz

namespace LO.Modal

open System

variable {α : Type*}

structure Hilbert (α : Type*) where
  axioms : Set (Formula α)

class Hilbert.FiniteAxiomatizable (H : Hilbert α) where
  axioms_fin : Set.Finite H.axioms

variable {H H₁ H₂ : Hilbert α}

inductive Hilbert.Deduction (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}      : φ ∈ H.axioms → Deduction H φ
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | subst {φ} (s) : Deduction H φ → Deduction H (φ⟦s⟧)
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

namespace Hilbert.Deduction

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

instance : System.Lukasiewicz H where
  mdp := mdp
  imply₁ := imply₁
  imply₂ := imply₂
  elim_contra := ec

instance : System.Classical H where

instance : System.HasDiaDuality H := inferInstance

instance : System.Necessitation H := ⟨nec⟩

lemma maxm! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := ⟨maxm h⟩

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! φ⟦s⟧ := ⟨subst s h.some⟩

end Hilbert.Deduction


namespace Hilbert

open Deduction

namespace Deduction

variable {H : Hilbert α}

noncomputable def inducition!
  {motive      : (φ : Formula α) → H ⊢! φ → Sort*}
  (hMaxm       : ∀ {φ}, (h : φ ∈ H.axioms) → motive φ ⟨maxm h⟩)
  (hMdp        : ∀ {φ ψ}, {hpq : H ⊢! φ ➝ ψ} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (mdp! hpq hp))
  (hNec        : ∀ {φ}, {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (□φ) (nec! hp))
  (hSubst      : ∀ {φ} (s : Substitution α), {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (φ⟦s⟧) (subst! s hp))
  (hImply₁     : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact hNec (ih ⟨hp⟩)
  | subst s hp ih => exact hSubst s (ih ⟨hp⟩)
  | _ => aesop;

end Deduction


variable {H H₁ H₂ : Hilbert α}

abbrev theorems (H : Hilbert α) := System.theory H

lemma of_subset (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⊢! φ → H₂ ⊢! φ := by
  intro h;
  induction h using Deduction.inducition! with
  | hMaxm h => exact maxm! $ hs h;
  | hMdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | hNec ih => exact nec! ih;
  | hSubst s ih => exact subst! s ih;
  | _ => simp;

lemma weakerThan_of_dominate_axioms (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ) : H₁ ≤ₛ H₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.inducition! with
  | hMaxm h => exact hMaxm h;
  | hMdp ih₁ ih₂ => exact mdp! ih₁ ih₂;
  | hNec ih => exact nec! ih;
  | hSubst s ih => exact subst! s ih;
  | _ => simp;

lemma weakerThan_of_subset_axioms (hSubset : H₁.axioms ⊆ H₂.axioms) : H₁ ≤ₛ H₂ := by
  apply weakerThan_of_dominate_axioms;
  intro φ hp;
  exact ⟨Deduction.maxm $ hSubset hp⟩;

end Hilbert


end LO.Modal

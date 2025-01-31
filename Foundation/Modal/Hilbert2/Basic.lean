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
  (hSubst      : ∀ {φ} (s), {hp : H ⊢! φ} → (ihp : motive φ hp) → motive (φ⟦s⟧) (subst! s hp))
  (hImply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
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



namespace Hilbert

def axiomInstances (H : Hilbert α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction₂ (H : Hilbert α) : (Formula α) → Type _
  | maxm {φ}      : (φ ∈ H.axiomInstances) → Deduction₂ H φ
  | mdp {φ ψ}     : Deduction₂ H (φ ➝ ψ) → Deduction₂ H φ → Deduction₂ H ψ
  | nec {φ}       : Deduction₂ H φ → Deduction₂ H (□φ)
  | imply₁ φ ψ    : Deduction₂ H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction₂ H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction₂ H $ Axioms.ElimContra φ ψ

notation H " ⊢² " φ => Deduction₂ H φ


def Deductive₂ (H : Hilbert α) (φ) := Nonempty (H ⊢² φ)
notation H " ⊢²! " φ => Deductive₂ H φ

lemma Deduction₂.nec! {H : Hilbert α} {φ} (h : H ⊢²! φ) : H ⊢²! □φ := ⟨Deduction₂.nec h.some⟩


noncomputable def Deduction₂.inducition!
  {motive      : (φ : Formula α) → (H ⊢²! φ) → Sort*}
  (hMaxm       : ∀ {φ}, (h : φ ∈ H.axiomInstances) → motive φ ⟨maxm h⟩)
  (hMdp        : ∀ {φ ψ}, {hpq : H ⊢²! φ ➝ ψ} → {hp : H ⊢²! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ ⟨mdp hpq.some hp.some⟩)
  (hNec        : ∀ {φ}, {hp : H ⊢²! φ} → (ihp : motive φ hp) → motive (□φ) ⟨nec hp.some⟩)
  (hImply₁     : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ ⟨imply₁ φ ψ⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ ⟨imply₂ φ ψ χ⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ⟩)
  : ∀ {φ}, (d : H ⊢²! φ) → motive φ d := by
  intro φ d;
  induction d.some with
  | maxm h => exact hMaxm h
  | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | nec hp ih => exact hNec (ih ⟨hp⟩)
  | _ => aesop;


lemma deductive₂_of_deductive : H ⊢! φ → H ⊢²! φ := by
  intro h;
  induction h using Deduction.inducition! with
  | hMaxm h => exact ⟨Deduction₂.maxm (mem_axiomInstances_of_mem_axioms (by assumption))⟩;
  | hMdp ih₁ ih₂ => exact ⟨Deduction₂.mdp ih₁.some ih₂.some⟩;
  | hNec ih => exact ⟨Deduction₂.nec ih.some⟩;
  | @hSubst φ s h₁ h₂ => sorry;
    /-
    obtain ⟨d₂⟩ := h₂;
    constructor;
    cases d₂;
    . sorry;
    . sorry;
    . sorry;
    . apply Deduction₂.imply₁;
    . apply Deduction₂.imply₂;
    . apply Deduction₂.ec;
    -/
  | hImply₁ => exact ⟨Deduction₂.imply₁ _ _⟩;
  | hImply₂ => exact ⟨Deduction₂.imply₂ _ _ _⟩;
  | hElimContra => exact ⟨Deduction₂.ec _ _⟩;

lemma deductive_of_deductive₂ : (H ⊢²! φ) → (H ⊢! φ) := by
  intro h;
  induction h using Deduction₂.inducition! with
  | hMaxm h =>
    obtain ⟨ψ, h, ⟨s, rfl⟩⟩ := h;
    exact Deduction.subst! s $ Deduction.maxm! h;
  | hMdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | hNec ih => exact nec! ih;
  | _ => simp;

theorem iff_deductive_deductive₂ : H ⊢! φ ↔ H ⊢²! φ := ⟨deductive₂_of_deductive, deductive_of_deductive₂⟩

end Hilbert


/-
namespace Hilbert

def Deduction.isSubstless : H ⊢ φ → Prop
  | subst _ _ => False
  | _ => True

def SubstlessDeduction (H : Hilbert α) (φ : Formula α) := { d : H ⊢ φ // Deduction.isSubstless d }
notation H " ⊢ˢ " φ => SubstlessDeduction H φ

open Deduction in
noncomputable def SubstlessDeduction.rec {motive : Formula α → Sort*}
  {motive      : (φ : Formula α) → (H ⊢ˢ φ) → Sort*}
  (hMdp        : ∀ {φ ψ}, {hpq : H ⊢ˢ (φ ➝ ψ)} → {hp : H ⊢ˢ φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ ⟨.mdp hpq.1 hp.1, by simp [isSubstless]⟩)
  (hNec        : ∀ {φ}, {hp : H ⊢ˢ φ} → (ihp : motive φ hp) → motive (□φ) ⟨.nec hp.1, by simp [isSubstless]⟩)
  (hImply₁     : ∀ {φ ψ}, motive (φ ➝ ψ ➝ φ) $ ⟨imply₁ φ ψ, by simp [isSubstless]⟩)
  (hImply₂     : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) $ ⟨imply₂ φ ψ χ, by simp [isSubstless]⟩)
  (hElimContra : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ ⟨ec φ ψ, by simp [isSubstless]⟩)
  : ∀ {φ}, (d : H ⊢ˢ φ) → motive φ d := by
  rintro φ ⟨d, hd⟩;
  induction d with
  | subst s hp ih => simp [isSubstless] at hd;
  -- | maxm h => exact hMaxm h
  -- | mdp hpq hp ihpq ihp => exact hMdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | @nec ψ hp ih =>
    have := ih ?_;
    have := @hNec ψ;
    sorry;
    . sorry;
  | _ => sorry;
  -- | _ => aesop;

def SubstlessDeductive (H : Hilbert α) (φ) := Nonempty (SubstlessDeduction H φ)
notation H:90 " ⊢ˢ! " φ:90 => SubstlessDeductive H φ

end Hilbert
-/

end LO.Modal

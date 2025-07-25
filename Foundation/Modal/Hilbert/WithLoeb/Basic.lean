import Foundation.Modal.Entailment.K4Loeb
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

namespace Hilbert

protected structure WithLoeb (α) where
  axioms : Set (Formula α)

namespace WithLoeb

variable {H H₁ H₂ : Hilbert.WithLoeb α} {φ ψ : Formula α}

abbrev axiomInstances (H : Hilbert.WithLoeb α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction (H : Hilbert.WithLoeb α) : (Formula α) → Type u
  | axm {φ} (s : Substitution _) : φ ∈ H.axioms → Deduction H (φ⟦s⟧)
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | nec {φ}       : Deduction H φ → Deduction H (□φ)
  | loeb {φ}      : Deduction H (□φ ➝ φ) → Deduction H φ
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

instance : Entailment (Formula α) (Hilbert.WithLoeb α) := ⟨Deduction⟩

def Deduction.axm' {H : Hilbert.WithLoeb α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Deduction.axm _ h;

section

variable {H : Hilbert.WithLoeb α}

instance : Entailment.Lukasiewicz H where
  mdp := .mdp
  imply₁ := .imply₁
  imply₂ := .imply₂
  elimContra := .ec
instance : Entailment.Necessitation H where
  nec := .nec
instance : Entailment.LoebRule H where
  loeb := .loeb

protected lemma rec!
  {motive   : (φ : Formula α) → (H ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ H.axioms) → motive (φ⟦s⟧) ⟨.axm s h⟩)
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : H ⊢! φ ➝ ψ} → {hφ : H ⊢! φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : H ⊢! φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (loeb     : ∀ {φ}, {hφψ : H ⊢! □φ ➝ φ} → motive (□φ ➝ φ) hφψ → motive (φ) (loeb! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  rintro φ ⟨d⟩;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
  | nec hφψ ihφ => apply nec ihφ
  | loeb hφψ ihφψ => apply loeb ihφψ
  | imply₁ φ ψ => apply imply₁
  | imply₂ φ ψ χ => apply imply₂
  | ec φ ψ => apply ec;

lemma axm! {φ} (s) (h : φ ∈ H.axioms) : H ⊢! (φ⟦s⟧) := ⟨.axm s h⟩

lemma axm'! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := by simpa using axm! Substitution.id h

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! (φ⟦s⟧) := by
  induction h using WithLoeb.rec! with
  | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
  | @axm φ s' h => rw [(show φ⟦s'⟧⟦s⟧ = φ⟦s' ∘ s⟧ by simp)]; apply axm!; exact h;
  | @loeb φ ψ h => apply loeb!; simpa;
  | @nec φ h => apply nec!; simpa;
  | _ => simp;

lemma weakerThan_of_provable_axioms (hs : H₂ ⊢!* H₁.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_iff.mpr;
  intro φ h;
  induction h using WithLoeb.rec! with
  | @axm φ s h => apply subst!; apply @hs φ h;
  | @loeb φ ψ h => apply loeb!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | @nec φ h => apply nec!; simpa;
  | _ => simp;

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_of_provable_axioms;
  intro φ h;
  apply axm'!;
  exact hs h;

end


section

abbrev logic (H : Hilbert.WithLoeb α) : Logic α := Entailment.theory H

@[simp high]
lemma iff_logic_provable_provable : H.logic ⊢! φ ↔ H ⊢! φ := by simp [logic, Entailment.theory, Set.mem_setOf_eq];

instance [H₁ ⪯ H₂] : H₁.logic ⪯ H₂.logic := by
  apply weakerThan_iff.mpr;
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq];
  apply WeakerThan.wk;
  infer_instance;

instance [H₁ ⪱ H₂] : H₁.logic ⪱ H₂.logic := by
  apply strictlyWeakerThan_iff.mpr;
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq, Logic.iff_unprovable];
  apply strictlyWeakerThan_iff.mp;
  infer_instance;

instance [H₁ ≊ H₂] : H₁.logic ≊ H₂.logic := by
  apply Equiv.iff.mpr;
  simp only [theory, Logic.iff_provable, Set.mem_setOf_eq];
  apply Equiv.iff.mp;
  infer_instance;

end


section

variable [DecidableEq α]

class HasK (H : Hilbert.WithLoeb α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_K : Axioms.K (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [DecidableEq α] [H.HasK] : Entailment.HasAxiomK H where
  K φ ψ := by
    simpa [HasK.ne_pq] using Deduction.axm
      (φ := Axioms.K (.atom (HasK.p H)) (.atom (HasK.q H)))
      (s := λ b =>
        if (HasK.p H) = b then φ
        else if (HasK.q H) = b then ψ
        else (.atom b))
      HasK.mem_K;


class HasFour (H : Hilbert.WithLoeb α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    simpa using Deduction.axm
      (φ := Axioms.Four (.atom (HasFour.p H)))
      (s := λ b => if (HasFour.p H) = b then φ else (.atom b))
      HasFour.mem_Four;

end

end WithLoeb

end Hilbert


protected abbrev Hilbert.K4Loeb : Hilbert.WithLoeb ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev K4Loeb := Hilbert.K4Loeb.logic
instance : (Hilbert.K4Loeb).HasK where p := 0; q := 1;
instance : (Hilbert.K4Loeb).HasFour where p := 0
instance : Entailment.K4Loeb (Hilbert.K4Loeb) where

end LO.Modal

import Foundation.Modal.Entailment.K4Loeb
import Foundation.Modal.Hilbert.Axiom
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.WithLoeb {α} (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → WithLoeb Ax (φ⟦s⟧)
| mdp {φ ψ}     : WithLoeb Ax (φ ➝ ψ) → WithLoeb Ax φ → WithLoeb Ax ψ
| nec {φ}       : WithLoeb Ax φ → WithLoeb Ax (□φ)
| loeb {φ}      : WithLoeb Ax (□φ ➝ φ) → WithLoeb Ax φ
| imply₁ φ ψ    : WithLoeb Ax $ Axioms.Imply₁ φ ψ
| imply₂ φ ψ χ  : WithLoeb Ax $ Axioms.Imply₂ φ ψ χ
| ec φ ψ        : WithLoeb Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.WithLoeb

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : WithLoeb Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! {φ} (h : φ ∈ Ax) : WithLoeb Ax ⊢ φ := by simpa using axm! .id h;

instance : Entailment.Lukasiewicz (Hilbert.WithLoeb Ax) where
  imply₁ _ _ := by constructor; apply Hilbert.WithLoeb.imply₁;
  imply₂ _ _ _ := by constructor; apply Hilbert.WithLoeb.imply₂;
  elimContra _ _ := by constructor; apply Hilbert.WithLoeb.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.WithLoeb.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.WithLoeb Ax) where
  nec h := by constructor; apply Hilbert.WithLoeb.nec; exact h.1;

instance : Entailment.LoebRule (Hilbert.WithLoeb Ax) where
  loeb h := by constructor; apply Hilbert.WithLoeb.loeb; exact h.1;

instance : Logic.Substitution (Hilbert.WithLoeb Ax) where
  subst {φ} s h := by
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | nec hφ ihφ => apply nec ihφ;
    | loeb hφψ ihφψ => apply loeb ihφψ;
    | imply₁ φ ψ => apply imply₁;
    | imply₂ φ ψ χ => apply imply₂;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (WithLoeb Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (WithLoeb Ax) ⊢ φ ➝ ψ} → {hφ : (WithLoeb Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (WithLoeb Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (loeb     : ∀ {φ}, {hφψ : (WithLoeb Ax) ⊢ □φ ➝ φ} → motive (□φ ➝ φ) hφψ → motive (φ) (loeb! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : WithLoeb Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | loeb hφψ ihφψ => apply loeb; exact ihφψ (Logic.iff_provable.mpr hφψ);
  | imply₁ φ ψ => apply imply₁;
  | imply₂ φ ψ χ => apply imply₂;
  | ec φ ψ => apply ec;

lemma weakerThan_of_provable_axioms (hs : WithLoeb Ax₂ ⊢* Ax₁) : (WithLoeb Ax₁) ⪯ (WithLoeb Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using WithLoeb.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | loeb ihφψ => apply loeb!; simpa;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (WithLoeb Ax₁) ⪯ (WithLoeb Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply WithLoeb.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance instHasAxiomK [Ax.HasK] : Entailment.HasAxiomK (Hilbert.WithLoeb Ax) where
  K φ ψ := by
    constructor;
    simpa [HasK.ne_pq] using Hilbert.WithLoeb.axm
      (φ := Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := λ b => if (HasK.p Ax) = b then φ else if (HasK.q Ax) = b then ψ else (.atom b))
      (by exact HasK.mem_K);

instance instHasAxiomFour [Ax.HasFour] : Entailment.HasAxiomFour (Hilbert.WithLoeb Ax) where
  Four φ := by
    constructor;
    simpa using Hilbert.WithLoeb.axm
      (φ := Axioms.Four (.atom (HasFour.p Ax)))
      (s := λ b => if (HasFour.p Ax) = b then φ else (.atom b))
      (by exact HasFour.mem_Four);

end

end Hilbert.WithLoeb


section

open Hilbert.WithLoeb

protected abbrev K4Loeb.axioms : Axiom ℕ := {
  Axioms.K (.atom 0) (.atom 1),
  Axioms.Four (.atom 0)
}
namespace K4Loeb.axioms
instance : K4Loeb.axioms.HasK where p := 0; q := 1;
instance : K4Loeb.axioms.HasFour where p := 0;
end K4Loeb.axioms
protected abbrev K4Loeb := Hilbert.WithLoeb K4Loeb.axioms
instance : Entailment.K4Loeb Modal.K4Loeb where

end

end LO.Modal

import Foundation.Modal.Entailment.K4Henkin
import Foundation.Modal.Hilbert.Axiom
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

inductive Hilbert.WithHenkin {α} (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → WithHenkin Ax (φ⟦s⟧)
| mdp {φ ψ}     : WithHenkin Ax (φ ➝ ψ) → WithHenkin Ax φ → WithHenkin Ax ψ
| nec {φ}       : WithHenkin Ax φ → WithHenkin Ax (□φ)
| henkin {φ}    : WithHenkin Ax (□φ ⭤ φ) → WithHenkin Ax φ
| imply₁ φ ψ    : WithHenkin Ax $ Axioms.Imply₁ φ ψ
| imply₂ φ ψ χ  : WithHenkin Ax $ Axioms.Imply₂ φ ψ χ
| ec φ ψ        : WithHenkin Ax $ Axioms.ElimContra φ ψ

namespace Hilbert.WithHenkin

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : WithHenkin Ax ⊢! φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! {φ} (h : φ ∈ Ax) : WithHenkin Ax ⊢! φ := by simpa using axm! .id h;

instance : Entailment.Lukasiewicz (Hilbert.WithHenkin Ax) where
  imply₁ _ _ := by constructor; apply Hilbert.WithHenkin.imply₁;
  imply₂ _ _ _ := by constructor; apply Hilbert.WithHenkin.imply₂;
  elimContra _ _ := by constructor; apply Hilbert.WithHenkin.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.WithHenkin.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Entailment.Necessitation (Hilbert.WithHenkin Ax) where
  nec h := by constructor; apply Hilbert.WithHenkin.nec; exact h.1;

instance : Entailment.HenkinRule (Hilbert.WithHenkin Ax) where
  henkin h := by constructor; apply Hilbert.WithHenkin.henkin; exact h.1;

instance : Logic.Substitution (Hilbert.WithHenkin Ax) where
  subst {φ} s h := by
    constructor;
    replace h := h.1;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | nec hφ ihφ => apply nec ihφ;
    | henkin hφψ ihφψ => apply henkin ihφψ;
    | imply₁ φ ψ => apply imply₁;
    | imply₂ φ ψ χ => apply imply₂;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (WithHenkin Ax ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (WithHenkin Ax) ⊢! φ ➝ ψ} → {hφ : (WithHenkin Ax) ⊢! φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (WithHenkin Ax) ⊢! φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (henkin   : ∀ {φ}, {hφψ : (WithHenkin Ax) ⊢! □φ ⭤ φ} → motive (□φ ⭤ φ) hφψ → motive (φ) (henkin! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : WithHenkin Ax ⊢! φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | henkin hφψ ihφψ => apply henkin; exact ihφψ (Logic.iff_provable.mpr hφψ);
  | imply₁ φ ψ => apply imply₁;
  | imply₂ φ ψ χ => apply imply₂;
  | ec φ ψ => apply ec;

lemma weakerThan_of_provable_axioms (hs : WithHenkin Ax₂ ⊢!* Ax₁) : (WithHenkin Ax₁) ⪯ (WithHenkin Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using WithHenkin.rec! with
  | axm h => apply Logic.subst!; apply hs; assumption;
  | henkin ihφψ => apply henkin!; simpa;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (WithHenkin Ax₁) ⪯ (WithHenkin Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply WithHenkin.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance instHasAxiomK [Ax.HasK] : Entailment.HasAxiomK (Hilbert.WithHenkin Ax) where
  K φ ψ := by
    constructor;
    simpa [HasK.ne_pq] using Hilbert.WithHenkin.axm
      (φ := Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := λ b => if (HasK.p Ax) = b then φ else if (HasK.q Ax) = b then ψ else (.atom b))
      (by exact HasK.mem_K);

instance instHasAxiomFour [Ax.HasFour] : Entailment.HasAxiomFour (Hilbert.WithHenkin Ax) where
  Four φ := by
    constructor;
    simpa using Hilbert.WithHenkin.axm
      (φ := Axioms.Four (.atom (HasFour.p Ax)))
      (s := λ b => if (HasFour.p Ax) = b then φ else (.atom b))
      (by exact HasFour.mem_Four);

end

end Hilbert.WithHenkin


section

open Hilbert.WithHenkin

protected abbrev K4Henkin.axioms : Axiom ℕ := {
  Axioms.K (.atom 0) (.atom 1),
  Axioms.Four (.atom 0)
}

namespace K4Henkin.axioms
instance : K4Henkin.axioms.HasK where p := 0; q := 1;
instance : K4Henkin.axioms.HasFour where p := 0;
end K4Henkin.axioms

protected abbrev K4Henkin := Hilbert.WithHenkin K4Henkin.axioms
instance : Entailment.K4Henkin Modal.K4Henkin where

end

end LO.Modal

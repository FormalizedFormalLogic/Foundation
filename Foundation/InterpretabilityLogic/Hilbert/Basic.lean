import Foundation.InterpretabilityLogic.Logic.Basic
import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Hilbert.Axiom

namespace LO.InterpretabilityLogic

open
  LO.Entailment
  LO.Modal.Entailment
  LO.InterpretabilityLogic.Entailment

inductive Hilbert {α} (Ax : Axiom α) : Logic α
| axm {φ} (s : Substitution _) : φ ∈ Ax → Hilbert Ax (φ⟦s⟧)
| mdp {φ ψ}     : Hilbert Ax (φ ➝ ψ) → Hilbert Ax φ → Hilbert Ax ψ
| nec {φ}       : Hilbert Ax φ → Hilbert Ax (□φ)
| imply₁ φ ψ    : Hilbert Ax $ Axioms.Imply₁ φ ψ
| imply₂ φ ψ χ  : Hilbert Ax $ Axioms.Imply₂ φ ψ χ
| ec φ ψ        : Hilbert Ax $ Axioms.ElimContra φ ψ

namespace Hilbert

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : Hilbert Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply axm s h;

@[grind] lemma axm'! {φ} (h : φ ∈ Ax) : Hilbert Ax ⊢ φ := by simpa using axm! (idSubstitution _) h;

instance : Entailment.Lukasiewicz (Hilbert Ax) where
  imply₁ _ _ := by constructor; apply Hilbert.imply₁;
  imply₂ _ _ _ := by constructor; apply Hilbert.imply₂;
  elimContra _ _ := by constructor; apply Hilbert.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Modal.Entailment.Necessitation (Hilbert Ax) where
  nec h := by constructor; apply Hilbert.nec; exact h.1;

instance : Logic.Substitution (Hilbert Ax) where
  subst {φ} s h := by
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih => simpa using axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
    | nec hφ ihφ => apply nec ihφ;
    | imply₁ φ ψ => apply imply₁;
    | imply₂ φ ψ χ => apply imply₂;
    | ec φ ψ => apply ec;

protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Hilbert Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : Hilbert Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | imply₁ φ ψ => apply imply₁;
  | imply₂ φ ψ χ => apply imply₂;
  | ec φ ψ => apply ec;

lemma weakerThan_of_provable_axioms (hs : Hilbert Ax₂ ⊢* Ax₁) : (Hilbert Ax₁) ⪯ (Hilbert Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert Ax₁) ⪯ (Hilbert Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance [Ax.HasK] : Modal.Entailment.HasAxiomK (Hilbert Ax) where
  K φ ψ := by
    constructor;
    simpa [HasK.ne_pq] using Hilbert.axm
      (φ := Modal.Axioms.K (.atom (HasK.p Ax)) (.atom (HasK.q Ax)))
      (s := λ b => if (HasK.p Ax) = b then φ else if (HasK.q Ax) = b then ψ else (.atom b))
      (HasK.mem_K);

instance [Ax.HasL] : Modal.Entailment.HasAxiomL (Hilbert Ax) where
  L φ := by
    constructor;
    simpa using Hilbert.axm
      (φ := Modal.Axioms.L (.atom (HasL.p Ax)))
      (s := λ b => if (HasL.p Ax) = b then φ else (.atom b))
      (HasL.mem_L);

instance [Ax.HasJ1] : InterpretabilityLogic.Entailment.HasAxiomJ1 (Hilbert Ax) where
  J1! {φ ψ} := by
    constructor;
    simpa [HasJ1.ne_pq] using Hilbert.axm
      (φ := InterpretabilityLogic.Axioms.J1 (.atom (HasJ1.p Ax)) (.atom (HasJ1.q Ax)))
      (s := λ b => if (HasJ1.p Ax) = b then φ else if (HasJ1.q Ax) = b then ψ else (.atom b))
      (HasJ1.mem_J1);

instance [Ax.HasJ2] : InterpretabilityLogic.Entailment.HasAxiomJ2 (Hilbert Ax) where
  J2! {φ ψ χ} := by
    constructor;
    simpa [HasJ2.ne_pq, HasJ2.ne_qr, HasJ2.ne_rp.symm] using Hilbert.axm
      (φ := InterpretabilityLogic.Axioms.J2 (.atom (HasJ2.p Ax)) (.atom (HasJ2.q Ax)) (.atom (HasJ2.r Ax)))
      (s := λ b =>
        if (HasJ2.p Ax) = b then φ
        else if (HasJ2.q Ax) = b then ψ
        else if (HasJ2.r Ax) = b then χ
        else (.atom b))
      $ HasJ2.mem_J2;

instance [Ax.HasJ3] : InterpretabilityLogic.Entailment.HasAxiomJ3 (Hilbert Ax) where
  J3! {φ ψ χ} := by
    constructor;
    simpa [HasJ3.ne_pq, HasJ3.ne_qr, HasJ3.ne_rp.symm] using Hilbert.axm
      (φ := InterpretabilityLogic.Axioms.J3 (.atom (HasJ3.p Ax)) (.atom (HasJ3.q Ax)) (.atom (HasJ3.r Ax)))
      (s := λ b =>
        if (HasJ3.p Ax) = b then φ
        else if (HasJ3.q Ax) = b then ψ
        else if (HasJ3.r Ax) = b then χ
        else (.atom b))
      $ HasJ3.mem_J3;

instance [Ax.HasJ4] : InterpretabilityLogic.Entailment.HasAxiomJ4 (Hilbert Ax) where
  J4! {φ ψ} := by
    constructor;
    simpa [HasJ4.ne_pq] using Hilbert.axm
      (φ := InterpretabilityLogic.Axioms.J4 (.atom (HasJ4.p Ax)) (.atom (HasJ4.q Ax)))
      (s := λ b => if (HasJ4.p Ax) = b then φ else if (HasJ4.q Ax) = b then ψ else (.atom b))
      (HasJ4.mem_J4);

instance [Ax.HasJ5] : InterpretabilityLogic.Entailment.HasAxiomJ5 (Hilbert Ax) where
  J5! {φ} := by
    constructor;
    simpa using Hilbert.axm
      (φ := InterpretabilityLogic.Axioms.J5 (.atom (HasJ5.p Ax)))
      (s := λ b => if (HasJ5.p Ax) = b then φ else (.atom b))
      (HasJ5.mem_J5);

end

end Hilbert


section

open Hilbert

protected abbrev CL.axioms : Axiom ℕ := {
  Modal.Axioms.K (.atom 0) (.atom 1),
  Modal.Axioms.L (.atom 0),
  InterpretabilityLogic.Axioms.J1 (.atom 0) (.atom 1),
  InterpretabilityLogic.Axioms.J2 (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.J3 (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.J4 (.atom 0) (.atom 1)
}
namespace CL.axioms
instance : CL.axioms.HasK where p := 0; q := 1;
instance : CL.axioms.HasL where p := 0;
instance : CL.axioms.HasJ1 where p := 0; q := 1;
instance : CL.axioms.HasJ2 where p := 0; q := 1; r := 2;
instance : CL.axioms.HasJ3 where p := 0; q := 1; r := 2;
instance : CL.axioms.HasJ4 where p := 0; q := 1;
end CL.axioms
protected abbrev CL := Hilbert CL.axioms
instance : Entailment.CL InterpretabilityLogic.CL where


protected abbrev IL.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.J5 (.atom 0)) CL.axioms
namespace IL.axioms
instance : IL.axioms.HasK where p := 0; q := 1;
instance : IL.axioms.HasL where p := 0;
instance : IL.axioms.HasJ1 where p := 0; q := 1;
instance : IL.axioms.HasJ2 where p := 0; q := 1; r := 2;
instance : IL.axioms.HasJ3 where p := 0; q := 1; r := 2;
instance : IL.axioms.HasJ4 where p := 0; q := 1;
instance : IL.axioms.HasJ5 where p := 0;
end IL.axioms
protected abbrev IL := Hilbert IL.axioms
instance : Entailment.IL InterpretabilityLogic.IL where

end

end LO.InterpretabilityLogic

import Foundation.InterpretabilityLogic.Logic.Basic
import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.ILM
import Foundation.InterpretabilityLogic.Entailment.ILP
import Foundation.InterpretabilityLogic.Entailment.ILW
import Foundation.InterpretabilityLogic.Entailment.ILWStar.Basic
import Foundation.InterpretabilityLogic.Entailment.ILWStar.M₀
import Foundation.InterpretabilityLogic.Entailment.ILM₀.Basic
import Foundation.InterpretabilityLogic.Entailment.ILWM₀
import Foundation.InterpretabilityLogic.Hilbert.Axiom

namespace LO.InterpretabilityLogic

open
  LO.Entailment
  LO.Modal.Entailment
  LO.InterpretabilityLogic.Entailment

inductive Hilbert.Basic {α} (Ax : Axiom α) : Logic α
| protected axm {φ} (s : Substitution _) : φ ∈ Ax → Hilbert.Basic Ax (φ⟦s⟧)
| protected mdp {φ ψ}     : Hilbert.Basic Ax (φ ➝ ψ) → Hilbert.Basic Ax φ → Hilbert.Basic Ax ψ
| protected nec {φ}       : Hilbert.Basic Ax φ → Hilbert.Basic Ax (□φ)
| protected implyK φ ψ    : Hilbert.Basic Ax $ Axioms.ImplyK φ ψ
| protected implyS φ ψ χ  : Hilbert.Basic Ax $ Axioms.ImplyS φ ψ χ
| protected ec φ ψ        : Hilbert.Basic Ax $ Axioms.ElimContra φ ψ
| protected axiomK φ ψ    : Hilbert.Basic Ax $ Modal.Axioms.K φ ψ
| protected axiomL φ      : Hilbert.Basic Ax $ Modal.Axioms.L φ

namespace Hilbert.Basic

variable {Ax Ax₁ Ax₂ : Axiom α}

@[grind ⇒] lemma axm! {φ} (s : Substitution _) (h : φ ∈ Ax) : Hilbert.Basic Ax ⊢ φ⟦s⟧ := by
  apply Logic.iff_provable.mpr;
  apply Basic.axm s h;

@[grind ⇒] lemma axm'! {φ} (h : φ ∈ Ax) : Hilbert.Basic Ax ⊢ φ := by simpa using axm! (idSubstitution _) h;

instance : Entailment.Lukasiewicz (Hilbert.Basic Ax) where
  implyK {_ _} := by constructor; apply Hilbert.Basic.implyK;
  implyS {_ _ _} := by constructor; apply Hilbert.Basic.implyS;
  elimContra {_ _} := by constructor; apply Hilbert.Basic.ec;
  mdp h₁ h₂ := by
    constructor;
    apply Hilbert.Basic.mdp;
    . exact h₁.1;
    . exact h₂.1;

instance : Modal.Entailment.GL (Hilbert.Basic Ax) where
  nec h := by constructor; apply Hilbert.Basic.nec; exact h.1;
  K φ ψ := by constructor; apply Hilbert.Basic.axiomK;
  L φ := by constructor; apply Hilbert.Basic.axiomL;

instance : Logic.Substitution (Hilbert.Basic Ax) where
  subst {φ} s h := by
    rw [Logic.iff_provable] at h ⊢;
    induction h with
    | @axm _ s' ih        => simpa using Basic.axm (s := s' ∘ s) ih;
    | mdp hφψ hφ ihφψ ihφ => apply Basic.mdp ihφψ ihφ;
    | nec hφ ihφ          => apply Basic.nec ihφ;
    | implyK φ ψ          => apply Basic.implyK;
    | implyS φ ψ χ        => apply Basic.implyS;
    | ec φ ψ              => apply Basic.ec;
    | axiomK φ ψ          => apply Basic.axiomK;
    | axiomL φ            => apply Basic.axiomL;

protected lemma rec!
  {motive   : (φ : Formula α) → (Hilbert.Basic Ax ⊢ φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ Ax) → motive (φ⟦s⟧) (by grind))
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : (Hilbert.Basic Ax) ⊢ φ ➝ ψ} → {hφ : (Hilbert.Basic Ax) ⊢ φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (nec      : ∀ {φ}, {hφψ : (Hilbert.Basic Ax) ⊢ φ} → motive (φ) hφψ → motive (□φ) (nec! hφψ))
  (implyK   : ∀ {φ ψ}, motive (Axioms.ImplyK φ ψ) $ by simp)
  (implyS   : ∀ {φ ψ χ}, motive (Axioms.ImplyS φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  (axiomK   : ∀ {φ ψ}, motive (Modal.Axioms.K φ ψ) $ by simp)
  (axiomL   : ∀ {φ}, motive (Modal.Axioms.L φ) $ by simp)
  : ∀ {φ}, (d : Hilbert.Basic Ax ⊢ φ) → motive φ d := by
  rintro φ d;
  replace d := Logic.iff_provable.mp d;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ =>
    apply mdp;
    . exact ihφψ (Logic.iff_provable.mpr hφψ);
    . exact ihφ (Logic.iff_provable.mpr hφ);
  | nec hφ ihφ => apply nec; exact ihφ (Logic.iff_provable.mpr hφ);
  | _ => grind

lemma weakerThan_of_provable_axioms (hs : Hilbert.Basic Ax₂ ⊢* Ax₁) : (Hilbert.Basic Ax₁) ⪯ (Hilbert.Basic Ax₂) := by
  apply Entailment.weakerThan_iff.mpr;
  intro φ h;
  induction h using Hilbert.Basic.rec! with
  | axm h => apply Logic.subst; apply hs; assumption;
  | nec ihφ => apply nec!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma equiv_of_provable_axioms (h₁ : Hilbert.Basic Ax₂ ⊢* Ax₁) (h₂ : Hilbert.Basic Ax₁ ⊢* Ax₂) : (Hilbert.Basic Ax₁) ≊ (Hilbert.Basic Ax₂) := by
  apply Equiv.antisymm;
  constructor <;>
  . apply weakerThan_of_provable_axioms;
    assumption;

lemma weakerThan_of_subset_axioms (h : Ax₁ ⊆ Ax₂) : (Hilbert.Basic Ax₁) ⪯ (Hilbert.Basic Ax₂) := by
  apply weakerThan_of_provable_axioms;
  intro φ hφ;
  apply Hilbert.Basic.axm'!;
  apply h;
  assumption;

open Axiom


section

variable [DecidableEq α]

instance [Ax.HasJ1] : InterpretabilityLogic.Entailment.HasAxiomJ1 (Hilbert.Basic Ax) where
  J1! {φ ψ} := by
    constructor;
    simpa [HasJ1.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J1 (.atom (HasJ1.p Ax)) (.atom (HasJ1.q Ax)))
      (s := λ b => if (HasJ1.p Ax) = b then φ else if (HasJ1.q Ax) = b then ψ else (.atom b))
      (HasJ1.mem_J1);

instance [Ax.HasJ2] : InterpretabilityLogic.Entailment.HasAxiomJ2 (Hilbert.Basic Ax) where
  J2! {φ ψ χ} := by
    constructor;
    simpa [HasJ2.ne_pq, HasJ2.ne_qr, HasJ2.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J2 (.atom (HasJ2.p Ax)) (.atom (HasJ2.q Ax)) (.atom (HasJ2.r Ax)))
      (s := λ b =>
        if (HasJ2.p Ax) = b then φ
        else if (HasJ2.q Ax) = b then ψ
        else if (HasJ2.r Ax) = b then χ
        else (.atom b))
      $ HasJ2.mem_J2;

instance [Ax.HasJ3] : InterpretabilityLogic.Entailment.HasAxiomJ3 (Hilbert.Basic Ax) where
  J3! {φ ψ χ} := by
    constructor;
    simpa [HasJ3.ne_pq, HasJ3.ne_qr, HasJ3.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J3 (.atom (HasJ3.p Ax)) (.atom (HasJ3.q Ax)) (.atom (HasJ3.r Ax)))
      (s := λ b =>
        if (HasJ3.p Ax) = b then φ
        else if (HasJ3.q Ax) = b then ψ
        else if (HasJ3.r Ax) = b then χ
        else (.atom b))
      $ HasJ3.mem_J3;

instance [Ax.HasJ4] : InterpretabilityLogic.Entailment.HasAxiomJ4 (Hilbert.Basic Ax) where
  J4! {φ ψ} := by
    constructor;
    simpa [HasJ4.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J4 (.atom (HasJ4.p Ax)) (.atom (HasJ4.q Ax)))
      (s := λ b => if (HasJ4.p Ax) = b then φ else if (HasJ4.q Ax) = b then ψ else (.atom b))
      (HasJ4.mem_J4);

instance [Ax.HasJ5] : InterpretabilityLogic.Entailment.HasAxiomJ5 (Hilbert.Basic Ax) where
  J5! {φ} := by
    constructor;
    simpa using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J5 (.atom (HasJ5.p Ax)))
      (s := λ b => if (HasJ5.p Ax) = b then φ else (.atom b))
      (HasJ5.mem_J5);

instance [Ax.HasM] : InterpretabilityLogic.Entailment.HasAxiomM (Hilbert.Basic Ax) where
  M! {φ ψ χ} := by
    constructor;
    simpa [HasM.ne_pq, HasM.ne_qr, HasM.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.M (.atom (HasM.p Ax)) (.atom (HasM.q Ax)) (.atom (HasM.r Ax)))
      (s := λ b =>
        if (HasM.p Ax) = b then φ
        else if (HasM.q Ax) = b then ψ
        else if (HasM.r Ax) = b then χ
        else (.atom b))
      $ HasM.mem_M;

instance [Ax.HasM] : InterpretabilityLogic.Entailment.HasAxiomM (Hilbert.Basic Ax) where
  M! {φ ψ χ} := by
    constructor;
    simpa [HasM.ne_pq, HasM.ne_qr, HasM.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.M (.atom (HasM.p Ax)) (.atom (HasM.q Ax)) (.atom (HasM.r Ax)))
      (s := λ b =>
        if (HasM.p Ax) = b then φ
        else if (HasM.q Ax) = b then ψ
        else if (HasM.r Ax) = b then χ
        else (.atom b))
      $ HasM.mem_M;

instance [Ax.HasM₀] : InterpretabilityLogic.Entailment.HasAxiomM₀ (Hilbert.Basic Ax) where
  M₀! {φ ψ χ} := by
    constructor;
    simpa [HasM₀.ne_pq, HasM₀.ne_qr, HasM₀.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.M₀ (.atom (HasM₀.p Ax)) (.atom (HasM₀.q Ax)) (.atom (HasM₀.r Ax)))
      (s := λ b =>
        if (HasM₀.p Ax) = b then φ
        else if (HasM₀.q Ax) = b then ψ
        else if (HasM₀.r Ax) = b then χ
        else (.atom b))
      $ HasM₀.mem_M₀;

instance [Ax.HasP] : InterpretabilityLogic.Entailment.HasAxiomP (Hilbert.Basic Ax) where
  P! {φ ψ} := by
    constructor;
    simpa [HasP.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.P (.atom (HasP.p Ax)) (.atom (HasP.q Ax)))
      (s := λ b => if (HasP.p Ax) = b then φ else if (HasP.q Ax) = b then ψ else (.atom b))
      (HasP.mem_P);

instance [Ax.HasW] : InterpretabilityLogic.Entailment.HasAxiomW (Hilbert.Basic Ax) where
  W! {φ ψ} := by
    constructor;
    simpa [HasW.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.W (.atom (HasW.p Ax)) (.atom (HasW.q Ax)))
      (s := λ b => if (HasW.p Ax) = b then φ else if (HasW.q Ax) = b then ψ else (.atom b))
      (HasW.mem_W);

instance [Ax.HasWStar] : InterpretabilityLogic.Entailment.HasAxiomWStar (Hilbert.Basic Ax) where
  WStar! {φ ψ χ} := by
    constructor;
    simpa [HasWStar.ne_pq, HasWStar.ne_qr, HasWStar.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.WStar (.atom (HasWStar.p Ax)) (.atom (HasWStar.q Ax)) (.atom (HasWStar.r Ax)))
      (s := λ b =>
        if (HasWStar.p Ax) = b then φ
        else if (HasWStar.q Ax) = b then ψ
        else if (HasWStar.r Ax) = b then χ
        else (.atom b))
      $ HasWStar.mem_WStar;

end

end Hilbert.Basic


section

open Axiom
open Hilbert.Basic

protected abbrev CL.axioms : Axiom ℕ := {
  InterpretabilityLogic.Axioms.J1 (.atom 0) (.atom 1),
  InterpretabilityLogic.Axioms.J2 (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.J3 (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.J4 (.atom 0) (.atom 1)
}
namespace CL.axioms
instance : CL.axioms.HasCLAxioms where p := 0; q := 1; r := 2;
end CL.axioms
protected abbrev CL := Hilbert.Basic CL.axioms
instance : Entailment.CL InterpretabilityLogic.CL where


protected abbrev IL.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.J5 (.atom 0)) CL.axioms
namespace IL.axioms
instance : IL.axioms.HasILAxioms where p := 0; q := 1; r := 2;
end IL.axioms
protected abbrev IL := Hilbert.Basic IL.axioms
instance : Entailment.IL InterpretabilityLogic.IL where


protected abbrev ILM.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace ILM.axioms
instance : ILM.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : ILM.axioms.HasM where p := 0; q := 1; r := 2;
end ILM.axioms
protected abbrev ILM := Hilbert.Basic ILM.axioms
instance : Entailment.ILM InterpretabilityLogic.ILM where


protected abbrev ILM₀.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M₀ (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace ILM₀.axioms
instance : ILM₀.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : ILM₀.axioms.HasM₀ where p := 0; q := 1; r := 2;
end ILM₀.axioms
protected abbrev ILM₀ := Hilbert.Basic ILM₀.axioms
instance : Entailment.ILM₀ InterpretabilityLogic.ILM₀ where


protected abbrev ILP.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.P (.atom 0) (.atom 1)) IL.axioms
namespace ILP.axioms
instance : ILP.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : ILP.axioms.HasP where p := 0; q := 1;
end ILP.axioms
protected abbrev ILP := Hilbert.Basic ILP.axioms
instance : Entailment.ILP InterpretabilityLogic.ILP where


protected abbrev ILW.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.W (.atom 0) (.atom 1)) IL.axioms
namespace ILW.axioms
instance : ILW.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : ILW.axioms.HasW where p := 0; q := 1;
end ILW.axioms

protected abbrev ILW := Hilbert.Basic ILW.axioms
instance : Entailment.ILW InterpretabilityLogic.ILW where


protected abbrev ILWStar.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.WStar (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace ILWStar.axioms
instance : ILWStar.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : ILWStar.axioms.HasWStar where p := 0; q := 1; r := 2
end ILWStar.axioms
protected abbrev ILWStar := Hilbert.Basic ILWStar.axioms
instance : Entailment.ILWStar InterpretabilityLogic.ILWStar where


protected abbrev ILWM₀.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M₀ (.atom 0) (.atom 1) (.atom 2)) ILW.axioms
namespace ILWM₀.axioms
instance : ILWM₀.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := ILW.axioms) (by tauto)
instance : ILWM₀.axioms.HasM₀ where p := 0; q := 1; r := 2
end ILWM₀.axioms
protected abbrev ILWM₀ := Hilbert.Basic ILWM₀.axioms
instance : Entailment.ILWM₀ InterpretabilityLogic.ILWM₀ where

instance : InterpretabilityLogic.ILWStar ≊ InterpretabilityLogic.ILWM₀ := by
  apply equiv_of_provable_axioms;
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      Entailment.WStar,
      Entailment.J1,
      Entailment.J2,
      Entailment.J3,
      Entailment.J4,
      Entailment.J5,
    ];
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      Entailment.W,
      Entailment.M₀,
      Entailment.J1,
      Entailment.J2,
      Entailment.J3,
      Entailment.J4,
      Entailment.J5,
    ];

end

end LO.InterpretabilityLogic

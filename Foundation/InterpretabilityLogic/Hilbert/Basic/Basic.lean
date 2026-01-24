import Foundation.InterpretabilityLogic.Logic.Basic
import Foundation.InterpretabilityLogic.Entailment
import Foundation.InterpretabilityLogic.Hilbert.Axiom
import Foundation.Propositional.Entailment.Cl.Łukasiewicz

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

instance : Entailment.Łukasiewicz (Hilbert.Basic Ax) where
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
  axiomJ1! {φ ψ} := by
    constructor;
    simpa [HasJ1.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J1 (.atom (HasJ1.p Ax)) (.atom (HasJ1.q Ax)))
      (s := λ b => if (HasJ1.p Ax) = b then φ else if (HasJ1.q Ax) = b then ψ else (.atom b))
      (HasJ1.mem_J1);

instance [Ax.HasJ2] : InterpretabilityLogic.Entailment.HasAxiomJ2 (Hilbert.Basic Ax) where
  axiomJ2! {φ ψ χ} := by
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
  axiomJ3! {φ ψ χ} := by
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
  axiomJ4! {φ ψ} := by
    constructor;
    simpa [HasJ4.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J4 (.atom (HasJ4.p Ax)) (.atom (HasJ4.q Ax)))
      (s := λ b => if (HasJ4.p Ax) = b then φ else if (HasJ4.q Ax) = b then ψ else (.atom b))
      (HasJ4.mem_J4);

instance [Ax.HasJ5] : InterpretabilityLogic.Entailment.HasAxiomJ5 (Hilbert.Basic Ax) where
  axiomJ5! {φ} := by
    constructor;
    simpa using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.J5 (.atom (HasJ5.p Ax)))
      (s := λ b => if (HasJ5.p Ax) = b then φ else (.atom b))
      (HasJ5.mem_J5);

instance [Ax.HasM] : InterpretabilityLogic.Entailment.HasAxiomM (Hilbert.Basic Ax) where
  axiomM! {φ ψ χ} := by
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
  axiomM! {φ ψ χ} := by
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
  axiomM₀! {φ ψ χ} := by
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
  axiomP! {φ ψ} := by
    constructor;
    simpa [HasP.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.P (.atom (HasP.p Ax)) (.atom (HasP.q Ax)))
      (s := λ b => if (HasP.p Ax) = b then φ else if (HasP.q Ax) = b then ψ else (.atom b))
      (HasP.mem_P);

instance [Ax.HasP₀] : InterpretabilityLogic.Entailment.HasAxiomP₀ (Hilbert.Basic Ax) where
  axiomP₀! {φ ψ} := by
    constructor;
    simpa [HasP₀.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.P₀ (.atom (HasP₀.p Ax)) (.atom (HasP₀.q Ax)))
      (s := λ b => if (HasP₀.p Ax) = b then φ else if (HasP₀.q Ax) = b then ψ else (.atom b))
      (HasP₀.mem_P₀);

instance [Ax.HasW] : InterpretabilityLogic.Entailment.HasAxiomW (Hilbert.Basic Ax) where
  axiomW! {φ ψ} := by
    constructor;
    simpa [HasW.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.W (.atom (HasW.p Ax)) (.atom (HasW.q Ax)))
      (s := λ b => if (HasW.p Ax) = b then φ else if (HasW.q Ax) = b then ψ else (.atom b))
      (HasW.mem_W);

instance [Ax.HasWstar] : InterpretabilityLogic.Entailment.HasAxiomWstar (Hilbert.Basic Ax) where
  axiomWstar! {φ ψ χ} := by
    constructor;
    simpa [HasWstar.ne_pq, HasWstar.ne_qr, HasWstar.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.Wstar (.atom (HasWstar.p Ax)) (.atom (HasWstar.q Ax)) (.atom (HasWstar.r Ax)))
      (s := λ b =>
        if (HasWstar.p Ax) = b then φ
        else if (HasWstar.q Ax) = b then ψ
        else if (HasWstar.r Ax) = b then χ
        else (.atom b))
      $ HasWstar.mem_Wstar;

instance [Ax.HasKW1Zero] : InterpretabilityLogic.Entailment.HasAxiomKW1Zero (Hilbert.Basic Ax) where
  axiomKW1Zero! {φ ψ} := by
    constructor;
    simpa [HasKW1Zero.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.KW1Zero (.atom (HasKW1Zero.p Ax)) (.atom (HasKW1Zero.q Ax)))
      (s := λ b => if (HasKW1Zero.p Ax) = b then φ else if (HasKW1Zero.q Ax) = b then ψ else (.atom b))
      (HasKW1Zero.mem_KW1Zero);

instance [Ax.HasKW2] : InterpretabilityLogic.Entailment.HasAxiomKW2 (Hilbert.Basic Ax) where
  axiomKW2! {φ ψ} := by
    constructor;
    simpa [HasKW2.ne_pq] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.KW2 (.atom (HasKW2.p Ax)) (.atom (HasKW2.q Ax)))
      (s := λ b => if (HasKW2.p Ax) = b then φ else if (HasKW2.q Ax) = b then ψ else (.atom b))
      (HasKW2.mem_KW2);

instance [Ax.HasF] : InterpretabilityLogic.Entailment.HasAxiomF (Hilbert.Basic Ax) where
  axiomF! {φ} := by
    constructor;
    simpa using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.F (.atom (HasF.p Ax)))
      (s := λ b => if (HasF.p Ax) = b then φ else (.atom b))
      (HasF.mem_F);

instance [Ax.HasR] : InterpretabilityLogic.Entailment.HasAxiomR (Hilbert.Basic Ax) where
  axiomR! {φ ψ χ} := by
    constructor;
    simpa [HasR.ne_pq, HasR.ne_qr, HasR.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.R (.atom (HasR.p Ax)) (.atom (HasR.q Ax)) (.atom (HasR.r Ax)))
      (s := λ b =>
        if (HasR.p Ax) = b then φ
        else if (HasR.q Ax) = b then ψ
        else if (HasR.r Ax) = b then χ
        else (.atom b))
      $ HasR.mem_R;

instance [Ax.HasRstar] : InterpretabilityLogic.Entailment.HasAxiomRstar (Hilbert.Basic Ax) where
  axiomRstar! {φ ψ χ} := by
    constructor;
    simpa [HasRstar.ne_pq, HasRstar.ne_qr, HasRstar.ne_rp.symm] using Hilbert.Basic.axm
      (φ := InterpretabilityLogic.Axioms.Rstar (.atom (HasRstar.p Ax)) (.atom (HasRstar.q Ax)) (.atom (HasRstar.r Ax)))
      (s := λ b =>
        if (HasRstar.p Ax) = b then φ
        else if (HasRstar.q Ax) = b then ψ
        else if (HasRstar.r Ax) = b then χ
        else (.atom b))
      $ HasRstar.mem_Rstar;


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


protected abbrev IL_M.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace IL_M.axioms
instance : IL_M.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_M.axioms.HasM where p := 0; q := 1; r := 2;
end IL_M.axioms
protected abbrev IL_M := Hilbert.Basic IL_M.axioms
instance : Entailment.IL_M InterpretabilityLogic.IL_M where


protected abbrev IL_M₀.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M₀ (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace IL_M₀.axioms
instance : IL_M₀.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_M₀.axioms.HasM₀ where p := 0; q := 1; r := 2;
end IL_M₀.axioms
protected abbrev IL_M₀ := Hilbert.Basic IL_M₀.axioms
instance : Entailment.IL_M₀ InterpretabilityLogic.IL_M₀ where


protected abbrev IL_P.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.P (.atom 0) (.atom 1)) IL.axioms
namespace IL_P.axioms
instance : IL_P.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_P.axioms.HasP where p := 0; q := 1;
end IL_P.axioms
protected abbrev IL_P := Hilbert.Basic IL_P.axioms
instance : Entailment.IL_P InterpretabilityLogic.IL_P where


protected abbrev IL_P₀.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.P₀ (.atom 0) (.atom 1)) IL.axioms
namespace IL_P₀.axioms
instance : IL_P₀.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_P₀.axioms.HasP₀ where p := 0; q := 1;
end IL_P₀.axioms
protected abbrev IL_P₀ := Hilbert.Basic IL_P₀.axioms
instance : Entailment.IL InterpretabilityLogic.IL_P₀ where


protected abbrev IL_W.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.W (.atom 0) (.atom 1)) IL.axioms
namespace IL_W.axioms
instance : IL_W.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_W.axioms.HasW where p := 0; q := 1;
end IL_W.axioms

protected abbrev IL_W := Hilbert.Basic IL_W.axioms
instance : Entailment.IL_W InterpretabilityLogic.IL_W where


protected abbrev IL_Wstar.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.Wstar (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace IL_Wstar.axioms
instance : IL_Wstar.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_Wstar.axioms.HasWstar where p := 0; q := 1; r := 2
end IL_Wstar.axioms
protected abbrev IL_Wstar := Hilbert.Basic IL_Wstar.axioms
instance : Entailment.IL_Wstar InterpretabilityLogic.IL_Wstar where


protected abbrev IL_M₀_W.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.M₀ (.atom 0) (.atom 1) (.atom 2)) IL_W.axioms
namespace IL_M₀_W.axioms
instance : IL_M₀_W.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL_W.axioms) (by tauto)
instance : IL_M₀_W.axioms.HasM₀ where p := 0; q := 1; r := 2
instance : IL_M₀_W.axioms.HasW where p := 0; q := 1;
end IL_M₀_W.axioms
protected abbrev IL_M₀_W := Hilbert.Basic IL_M₀_W.axioms
instance : Entailment.IL_M₀_W InterpretabilityLogic.IL_M₀_W where


instance : InterpretabilityLogic.IL_Wstar ≊ InterpretabilityLogic.IL_M₀_W := by
  apply equiv_of_provable_axioms;
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomWstar,
    ];
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomW,
      axiomM₀,
    ];

instance : InterpretabilityLogic.IL_W ⪯ InterpretabilityLogic.IL_Wstar := by
  apply weakerThan_of_provable_axioms;
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomW,
    ];

protected abbrev IL_F.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.F (.atom 0)) IL.axioms
namespace IL_F.axioms
instance : IL_F.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_F.axioms.HasF where p := 0;
end IL_F.axioms
protected abbrev IL_F := Hilbert.Basic IL_F.axioms


protected abbrev IL_KW1Zero.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.KW1Zero (.atom 0) (.atom 1)) IL.axioms
namespace IL_KW1Zero.axioms
instance : IL_KW1Zero.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_KW1Zero.axioms.HasKW1Zero where p := 0; q := 1;
end IL_KW1Zero.axioms
protected abbrev IL_KW1Zero := Hilbert.Basic IL_KW1Zero.axioms
instance : Entailment.IL_KW1Zero InterpretabilityLogic.IL_KW1Zero where


protected abbrev IL_KW2.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.KW2 (.atom 0) (.atom 1)) IL.axioms
namespace IL_KW2.axioms
instance : IL_KW2.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_KW2.axioms.HasKW2 where p := 0; q := 1;
end IL_KW2.axioms
protected abbrev IL_KW2 := Hilbert.Basic IL_KW2.axioms
instance : Entailment.IL_KW2 InterpretabilityLogic.IL_KW2 where


instance : InterpretabilityLogic.IL_KW1Zero ≊ InterpretabilityLogic.IL_KW2 := by
  apply equiv_of_provable_axioms;
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomKW1Zero,
    ];
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomKW2,
    ];


instance : InterpretabilityLogic.IL_KW2 ⪯ InterpretabilityLogic.IL_W := by
  apply weakerThan_of_provable_axioms;
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomKW2,
    ];

instance : InterpretabilityLogic.IL_F ⪯ InterpretabilityLogic.IL_KW2 := by
  apply weakerThan_of_provable_axioms;
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomF,
    ];

instance : InterpretabilityLogic.IL ⪯ InterpretabilityLogic.IL_F := by
  apply weakerThan_of_subset_axioms;
  simp;

protected abbrev IL_R.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.R (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace IL_R.axioms
instance : IL_R.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_R.axioms.HasR where p := 0; q := 1; r := 2
end IL_R.axioms
protected abbrev IL_R := Hilbert.Basic IL_R.axioms
instance : Entailment.IL_R InterpretabilityLogic.IL_R where

instance : InterpretabilityLogic.IL_P₀ ⪯ InterpretabilityLogic.IL_R := by
  apply weakerThan_of_provable_axioms;
  rintro φ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomP₀,
    ];

protected abbrev IL_R_W.axioms : Axiom ℕ := IL.axioms ∪ {
  InterpretabilityLogic.Axioms.R (.atom 0) (.atom 1) (.atom 2),
  InterpretabilityLogic.Axioms.W (.atom 0) (.atom 1)
}
namespace IL_R_W.axioms
instance : IL_R_W.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_R_W.axioms.HasR where p := 0; q := 1; r := 2
instance : IL_R_W.axioms.HasW where p := 0; q := 1;
end IL_R_W.axioms
protected abbrev IL_R_W := Hilbert.Basic IL_R_W.axioms
instance : Entailment.IL_R_W InterpretabilityLogic.IL_R_W where

protected abbrev IL_Rstar.axioms : Axiom ℕ := insert (InterpretabilityLogic.Axioms.Rstar (.atom 0) (.atom 1) (.atom 2)) IL.axioms
namespace IL_Rstar.axioms
instance : IL_Rstar.axioms.HasILAxioms := HasILAxioms.of_subset (Ax₁ := IL.axioms) (by tauto)
instance : IL_Rstar.axioms.HasRstar where p := 0; q := 1; r := 2
end IL_Rstar.axioms
protected abbrev IL_Rstar := Hilbert.Basic IL_Rstar.axioms
instance : Entailment.IL_Rstar InterpretabilityLogic.IL_Rstar where

instance : InterpretabilityLogic.IL_R_W ≊ InterpretabilityLogic.IL_Rstar := by
  apply equiv_of_provable_axioms;
  . rintro φ hφ;
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ;
    rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomR,
      axiomW,
    ];
  . rintro φ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [
      axiomJ1,
      axiomJ2,
      axiomJ3,
      axiomJ4,
      axiomJ5,
      axiomRstar,
    ];

end

end LO.InterpretabilityLogic

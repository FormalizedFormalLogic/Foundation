import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.EMCN
import Foundation.Logic.HilbertStyle.Lukasiewicz
import Foundation.Modal.Logic.Basic

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

namespace Hilbert

protected structure WithRE (α) where
  axioms : Set (Formula α)

namespace WithRE

variable {H H₁ H₂ : Hilbert.WithRE α} {φ ψ : Formula α}

abbrev axiomInstances (H : Hilbert.WithRE α) : Set (Formula α) := { φ⟦s⟧ | (φ ∈ H.axioms) (s : Substitution α) }

lemma mem_axiomInstances_of_mem_axioms {φ} (h : φ ∈ H.axioms) : φ ∈ H.axiomInstances := by
  use φ;
  constructor;
  . assumption;
  . use Substitution.id;
    simp;

inductive Deduction (H : Hilbert.WithRE α) : (Formula α) → Type u
  | axm {φ} (s : Substitution _) : φ ∈ H.axioms → Deduction H (φ⟦s⟧)
  | mdp {φ ψ}     : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | re {φ ψ}      : Deduction H (φ ⭤ ψ) → Deduction H (□φ ⭤ □ψ)
  | imply₁ φ ψ    : Deduction H $ Axioms.Imply₁ φ ψ
  | imply₂ φ ψ χ  : Deduction H $ Axioms.Imply₂ φ ψ χ
  | ec φ ψ        : Deduction H $ Axioms.ElimContra φ ψ

instance : Entailment (Formula α) (Hilbert.WithRE α) := ⟨Deduction⟩

def Deduction.axm' {H : Hilbert.WithRE α} {φ} (h : φ ∈ H.axioms) : Deduction H φ := by
  rw [(show φ = φ⟦.id⟧ by simp)]
  apply Deduction.axm _ h;

section

variable {H : Hilbert.WithRE α}

instance : Entailment.Lukasiewicz H where
  mdp := .mdp
  imply₁ := .imply₁
  imply₂ := .imply₂
  elimContra := .ec
instance : Entailment.E H where
  re := .re

protected lemma rec!
  {motive   : (φ : Formula α) → (H ⊢! φ) → Sort}
  (axm      : ∀ {φ : Formula α} (s), (h : φ ∈ H.axioms) → motive (φ⟦s⟧) ⟨.axm s h⟩)
  (mdp      : ∀ {φ ψ : Formula α}, {hφψ : H ⊢! φ ➝ ψ} → {hφ : H ⊢! φ} → motive (φ ➝ ψ) hφψ → motive φ hφ → motive ψ (hφψ ⨀ hφ))
  (re       : ∀ {φ ψ}, {hφψ : H ⊢! φ ⭤ ψ} → motive (φ ⭤ ψ) hφψ → motive (□φ ⭤ □ψ) (re! hφψ))
  (imply₁   : ∀ {φ ψ}, motive (Axioms.Imply₁ φ ψ) $ by simp)
  (imply₂   : ∀ {φ ψ χ}, motive (Axioms.Imply₂ φ ψ χ) $ by simp)
  (ec       : ∀ {φ ψ}, motive (Axioms.ElimContra φ ψ) $ by simp)
  : ∀ {φ}, (d : H ⊢! φ) → motive φ d := by
  rintro φ ⟨d⟩;
  induction d with
  | axm s h => apply axm s h;
  | mdp hφψ hφ ihφψ ihφ => apply mdp ihφψ ihφ;
  | re hφψ ihφψ => apply re ihφψ
  | imply₁ φ ψ => apply imply₁
  | imply₂ φ ψ χ => apply imply₂
  | ec φ ψ => apply ec;

lemma axm! {φ} (s) (h : φ ∈ H.axioms) : H ⊢! (φ⟦s⟧) := ⟨.axm s h⟩

lemma axm'! {φ} (h : φ ∈ H.axioms) : H ⊢! φ := by simpa using axm! Substitution.id h

lemma subst! {φ} (s) (h : H ⊢! φ) : H ⊢! (φ⟦s⟧) := by
  induction h using WithRE.rec! with
  | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
  | @axm φ s' h => rw [(show φ⟦s'⟧⟦s⟧ = φ⟦s' ∘ s⟧ by simp)]; apply axm!; exact h;
  | @re φ ψ h => apply re!; simpa;
  | _ => simp;

lemma weakerThan_of_provable_axioms (hs : H₂ ⊢!* H₁.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_iff.mpr;
  intro φ h;
  induction h using WithRE.rec! with
  | @axm φ s h => apply subst!; apply @hs φ h;
  | @re φ ψ h => apply re!; simpa;
  | mdp ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | _ => simp;

lemma weakerThan_of_subset_axioms (hs : H₁.axioms ⊆ H₂.axioms) : H₁ ⪯ H₂ := by
  apply weakerThan_of_provable_axioms;
  intro φ h;
  apply axm'!;
  exact hs h;

end


section

abbrev logic (H : Hilbert.WithRE α) : Logic α := Entailment.theory H

@[simp high]
lemma iff_logic_provable_provable : H.logic ⊢! φ ↔ H ⊢! φ := by simp [Entailment.theory, Logic.iff_provable];

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

class HasM (H : Hilbert.WithRE α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_m : Axioms.M (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasM] : Entailment.HasAxiomM H where
  M φ ψ := by
    simpa [HasM.ne_pq] using Deduction.axm
      (φ := Axioms.M (.atom (HasM.p H)) (.atom (HasM.q H)))
      (s := λ b =>
        if (HasM.p H) = b then φ
        else if (HasM.q H) = b then ψ
        else (.atom b))
      HasM.mem_m;


class HasC (H : Hilbert.WithRE α) where
  p : α
  q : α
  ne_pq : p ≠ q := by trivial;
  mem_c : Axioms.C (.atom p) (.atom q) ∈ H.axioms := by tauto;

instance [H.HasC] : Entailment.HasAxiomC H where
  C φ ψ := by
    simpa [HasC.ne_pq] using Deduction.axm
      (φ := Axioms.C (.atom (HasC.p H)) (.atom (HasC.q H)))
      (s := λ b =>
        if (HasC.p H) = b then φ
        else if (HasC.q H) = b then ψ
        else (.atom b))
      HasC.mem_c;


class HasN (H : Hilbert.WithRE α) where
  mem_n : Axioms.N ∈ H.axioms := by tauto;

instance [H.HasN] : Entailment.HasAxiomN H where
  N := by apply Deduction.axm'; simp [HasN.mem_n];


class HasK (H : Hilbert.WithRE α) where
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


class HasT (H : Hilbert.WithRE α) where
  p : α
  mem_T : Axioms.T (.atom p) ∈ H.axioms := by tauto;

instance [H.HasT] : Entailment.HasAxiomT H where
  T φ := by
    simpa using Deduction.axm
      (φ := Axioms.T (.atom (HasT.p H)))
      (s := λ b => if (HasT.p H) = b then φ else (.atom b))
      HasT.mem_T;

class HasD (H : Hilbert.WithRE α) where
  p : α
  mem_D : Axioms.D (.atom p) ∈ H.axioms := by tauto;

instance [H.HasD] : Entailment.HasAxiomD H where
  D φ := by
    simpa using Deduction.axm
      (φ := Axioms.D (.atom (HasD.p H)))
      (s := λ b => if (HasD.p H) = b then φ else (.atom b))
      HasD.mem_D;

class HasP (H : Hilbert.WithRE α) where
  mem_P : Axioms.P ∈ H.axioms := by tauto;

instance [H.HasP] : Entailment.HasAxiomP H where
  P := by simpa using Deduction.axm' (h := HasP.mem_P);


class HasFour (H : Hilbert.WithRE α) where
  p : α
  mem_Four : Axioms.Four (.atom p) ∈ H.axioms := by tauto;

instance [H.HasFour] : Entailment.HasAxiomFour H where
  Four φ := by
    simpa using Deduction.axm
      (φ := Axioms.Four (.atom (HasFour.p H)))
      (s := λ b => if (HasFour.p H) = b then φ else (.atom b))
      HasFour.mem_Four;

end

end WithRE

end Hilbert


protected abbrev Hilbert.E : Hilbert.WithRE ℕ := ⟨∅⟩
protected abbrev E : Logic ℕ := Entailment.theory Hilbert.E
notation "𝐄" => Modal.E
instance : Entailment.E Hilbert.E where


protected abbrev Hilbert.EM : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1)}⟩
protected abbrev EM : Logic ℕ := Entailment.theory Hilbert.EM
notation "𝐄𝐌" => Modal.EM
instance : Hilbert.EM.HasM where p := 0; q := 1
instance : Entailment.EM Hilbert.EM where


protected abbrev Hilbert.EC : Hilbert.WithRE ℕ := ⟨{Axioms.C (.atom 0) (.atom 1)}⟩
protected abbrev EC : Logic ℕ := Entailment.theory Hilbert.EC
notation "𝐄𝐂" => Modal.EC
instance : Hilbert.EC.HasC where p := 0; q := 1
instance : Entailment.EC Hilbert.EC where


protected abbrev Hilbert.EN : Hilbert.WithRE ℕ := ⟨{Axioms.N}⟩
protected abbrev EN : Logic ℕ := Entailment.theory Hilbert.EN
notation "𝐄𝐍" => Modal.EN
instance : Hilbert.EN.HasN where
instance : Entailment.EN Hilbert.EN where


protected abbrev Hilbert.EK : Hilbert.WithRE ℕ := ⟨{Axioms.K (.atom 0) (.atom 1)}⟩
protected abbrev EK : Logic ℕ := Entailment.theory Hilbert.EK
notation "𝐄𝐊" => Modal.EK
instance : Hilbert.EK.HasK where p := 0; q := 1
instance : Entailment.EK Hilbert.EK where


protected abbrev Hilbert.EMC : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1)}⟩
protected abbrev EMC : Logic ℕ := Entailment.theory Hilbert.EMC
notation "𝐄𝐌𝐂" => Modal.EMC
instance : Hilbert.EMC.HasM where p := 0; q := 1
instance : Hilbert.EMC.HasC where p := 0; q := 1
instance : Entailment.EMC Hilbert.EMC where


protected abbrev Hilbert.EMN : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.N}⟩
protected abbrev EMN : Logic ℕ := Entailment.theory Hilbert.EMN
notation "𝐄𝐌𝐍" => Modal.EMN
instance : Hilbert.EMN.HasM where p := 0; q := 1
instance : Hilbert.EMN.HasN where
instance : Entailment.EMN Hilbert.EMN where


protected abbrev Hilbert.ECN : Hilbert.WithRE ℕ := ⟨{Axioms.C (.atom 0) (.atom 1), Axioms.N}⟩
protected abbrev ECN : Logic ℕ := Entailment.theory Hilbert.ECN
notation "𝐄𝐂𝐍" => Modal.ECN
instance : Hilbert.ECN.HasC where p := 0; q := 1
instance : Hilbert.ECN.HasN where
instance : Entailment.ECN Hilbert.ECN where


protected abbrev Hilbert.EMCN : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1), Axioms.N}⟩
protected abbrev EMCN : Logic ℕ := Entailment.theory Hilbert.EMCN
notation "𝐄𝐌𝐂𝐍" => Modal.EMCN
instance : Hilbert.EMCN.HasM where p := 0; q := 1
instance : Hilbert.EMCN.HasC where p := 0; q := 1
instance : Hilbert.EMCN.HasN where
instance : Entailment.EMCN Hilbert.EMCN where


protected abbrev Hilbert.E4 : Hilbert.WithRE ℕ := ⟨{Axioms.Four (.atom 0)}⟩
protected abbrev E4 : Logic ℕ := Entailment.theory Hilbert.E4
notation "𝐄𝟒" => Modal.E4
instance : Hilbert.E4.HasFour where p := 0
instance : Entailment.E4 Hilbert.E4 where


protected abbrev Hilbert.ED : Hilbert.WithRE ℕ := ⟨{Axioms.D (.atom 0)}⟩
protected abbrev ED : Logic ℕ := Entailment.theory Hilbert.ED
instance : Hilbert.ED.HasD where p := 0
notation "𝐄𝐃" => Modal.ED


protected abbrev Hilbert.EP : Hilbert.WithRE ℕ := ⟨{Axioms.P}⟩
protected abbrev EP : Logic ℕ := Entailment.theory Hilbert.EP
notation "𝐄𝐏" => Modal.EP
instance : Hilbert.EP.HasP where


protected abbrev Hilbert.EMC4 : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.C (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev EMC4 : Logic ℕ := Entailment.theory Hilbert.EMC4
notation "𝐄𝐌𝐂𝟒" => Modal.EMC4
instance : Hilbert.EMC4.HasM where p := 0; q := 1
instance : Hilbert.EMC4.HasC where p := 0; q := 1
instance : Hilbert.EMC4.HasFour where p := 0
instance : Entailment.EMC4 Hilbert.EMC4 where


protected abbrev Hilbert.EK4 : Hilbert.WithRE ℕ := ⟨{Axioms.K (.atom 0) (.atom 1), Axioms.Four (.atom 0)}⟩
protected abbrev EK4 : Logic ℕ := Entailment.theory Hilbert.EK4
notation "𝐄𝐊𝟒" => Modal.EK4
instance : Hilbert.EK4.HasK where p := 0; q := 1
instance : Hilbert.EK4.HasFour where p := 0
instance : Entailment.EK4 Hilbert.EK4 where


protected abbrev Hilbert.EMT : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.T (.atom 0)}⟩
protected abbrev EMT : Logic ℕ := Entailment.theory Hilbert.EMT
notation "𝐄𝐌𝐓" => Modal.EMT
instance : Hilbert.EMT.HasM where p := 0; q := 1
instance : Hilbert.EMT.HasT where p := 0


protected abbrev Hilbert.EMT4 : Hilbert.WithRE ℕ := ⟨{Axioms.M (.atom 0) (.atom 1), Axioms.Four (.atom 0), Axioms.T (.atom 0)}⟩
/--
  - Sometimes called `S04`?
-/
protected abbrev EMT4 : Logic ℕ := Entailment.theory Hilbert.EMT4
notation "𝐄𝐌𝐓𝟒" => Modal.EMT4
instance : Hilbert.EMT4.HasM where p := 0; q := 1
instance : Hilbert.EMT4.HasFour where p := 0
instance : Hilbert.EMT4.HasT where p := 0
instance : Entailment.EMT4 Hilbert.EMT4 where


protected abbrev Hilbert.EMCN4 : Hilbert.WithRE ℕ := ⟨{
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.Four (.atom 0)
}⟩
protected abbrev EMCN4 : Logic ℕ := Entailment.theory Hilbert.EMCN4
notation "𝐄𝐌𝐂𝐍𝟒" => Modal.EMCN4
instance : Hilbert.EMCN4.HasM where p := 0; q := 1
instance : Hilbert.EMCN4.HasC where p := 0; q := 1
instance : Hilbert.EMCN4.HasN where
instance : Hilbert.EMCN4.HasFour where p := 0
instance : Entailment.EMCN Hilbert.EMCN4 where


protected abbrev Hilbert.EMCNT : Hilbert.WithRE ℕ := ⟨{
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0)
}⟩
/--
  Equivalent to `KT`
-/
protected abbrev EMCNT : Logic ℕ := Entailment.theory Hilbert.EMCNT
notation "𝐄𝐌𝐂𝐍𝐓" => Modal.EMCNT
instance : Hilbert.EMCNT.HasM where p := 0; q := 1
instance : Hilbert.EMCNT.HasC where p := 0; q := 1
instance : Hilbert.EMCNT.HasN where
instance : Hilbert.EMCNT.HasT where p := 0
instance : Entailment.EMCN Hilbert.EMCNT where


protected abbrev Hilbert.EMCNT4 : Hilbert.WithRE ℕ := ⟨{
  Axioms.M (.atom 0) (.atom 1),
  Axioms.C (.atom 0) (.atom 1),
  Axioms.N,
  Axioms.T (.atom 0),
  Axioms.Four (.atom 0)
}⟩
/--
  Equivalent to `S4`
-/
protected abbrev EMCNT4 : Logic ℕ := Entailment.theory Hilbert.EMCNT4
notation "𝐄𝐌𝐂𝐍𝐓𝟒" => Modal.EMCNT4
instance : Hilbert.EMCNT4.HasM where p := 0; q := 1
instance : Hilbert.EMCNT4.HasC where p := 0; q := 1
instance : Hilbert.EMCNT4.HasN where
instance : Hilbert.EMCNT4.HasT where p := 0
instance : Hilbert.EMCNT4.HasFour where p := 0
instance : Entailment.EMCN Hilbert.EMCNT4 where


end LO.Modal

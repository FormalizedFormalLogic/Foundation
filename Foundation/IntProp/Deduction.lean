import Foundation.Logic.HilbertStyle.Basic
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Formula

namespace LO.IntProp

variable {α : Type u}

structure Hilbert (α) where
  axioms : Theory α

namespace Hilbert

variable {H : Hilbert α}


section

class IncludeEFQ (H : Hilbert α) where
  include_EFQ : 𝗘𝗙𝗤 ⊆ H.axioms := by simp

class IncludeLEM (H : Hilbert α) where
  include_LEM : 𝗟𝗘𝗠 ⊆ H.axioms := by simp

class IncludeDNE (H : Hilbert α) where
  include_DNE : 𝗗𝗡𝗘 ⊆ H.axioms := by simp

end


inductive Deduction (H : Hilbert α) : Formula α → Type _
  | eaxm {φ}     : φ ∈ H.axioms → Deduction H φ
  | mdp {φ ψ}    : Deduction H (φ ➝ ψ) → Deduction H φ → Deduction H ψ
  | verum        : Deduction H $ ⊤
  | imply₁ φ ψ   : Deduction H $ φ ➝ ψ ➝ φ
  | imply₂ φ ψ χ : Deduction H $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | and₁ φ ψ     : Deduction H $ φ ⋏ ψ ➝ φ
  | and₂ φ ψ     : Deduction H $ φ ⋏ ψ ➝ ψ
  | and₃ φ ψ     : Deduction H $ φ ➝ ψ ➝ φ ⋏ ψ
  | or₁ φ ψ      : Deduction H $ φ ➝ φ ⋎ ψ
  | or₂ φ ψ      : Deduction H $ ψ ➝ φ ⋎ ψ
  | or₃ φ ψ χ    : Deduction H $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
  | neg_equiv φ  : Deduction H $ Axioms.NegEquiv φ

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

open Deduction
open Hilbert

section

instance : System.Minimal H where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  neg_equiv := neg_equiv

instance [H.IncludeEFQ] : System.HasAxiomEFQ H where
  efq _ := eaxm $ Set.mem_of_subset_of_mem IncludeEFQ.include_EFQ (by simp);

instance [H.IncludeLEM] : System.HasAxiomLEM H where
  lem _ := eaxm $ Set.mem_of_subset_of_mem IncludeLEM.include_LEM (by simp);

instance [H.IncludeDNE] : System.HasAxiomDNE H where
  dne _ := eaxm $ Set.mem_of_subset_of_mem IncludeDNE.include_DNE (by simp);

instance [H.IncludeEFQ] : System.Intuitionistic H where

instance [H.IncludeDNE] : System.Classical H where

instance [DecidableEq α] [H.IncludeEFQ] [H.IncludeLEM] : System.Classical H where

end


abbrev theorems (H : Hilbert α) : Set (Formula α) := System.theory H


section systems

variable (α)

protected abbrev Minimal : Hilbert α := ⟨∅⟩

protected abbrev Int : Hilbert α := ⟨𝗘𝗙𝗤⟩
instance : IncludeEFQ (Hilbert.Int α) where
instance : System.Intuitionistic (Hilbert.Int α) where

protected abbrev Cl : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠⟩
instance : IncludeLEM (α := α) (Hilbert.Cl α) where
instance : IncludeEFQ (α := α) (Hilbert.Cl α) where

/--
  `KC` from Chagrov & Zakharyaschev (1997)
-/
protected abbrev KC : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗪𝗟𝗘𝗠⟩
instance : IncludeEFQ (α := α) (Hilbert.KC α) where
instance : System.HasAxiomWeakLEM (Hilbert.KC α) where
  wlem φ := by apply eaxm; aesop;

/--
  `LC` from Chagrov & Zakharyaschev (1997)
-/
protected abbrev LC : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗗𝘂𝗺⟩
instance : IncludeEFQ (α := α) (Hilbert.LC α) where
instance : System.HasAxiomDummett (Hilbert.LC α) where
  dummett φ ψ := by apply eaxm; aesop;

-- MEMO: Minimal <ₛ WeakMinimal <ₛ WeakClassical <ₛ Classical

/--
  `WeakMinimal` from Ariola (2007)
-/
protected abbrev WeakMinimal : Hilbert α := ⟨𝗟𝗘𝗠⟩


/--
  `WeakClassical` from Ariola (2007)
-/
protected abbrev WeakClassical : Hilbert α := ⟨𝗣𝗲⟩

end systems


abbrev Consistent (H : Hilbert α) := System.Consistent H


namespace Deduction

open System

lemma eaxm! {H : Hilbert α} {φ : Formula α} (h : φ ∈ H.axioms) : H ⊢! φ := ⟨eaxm h⟩

noncomputable def rec! {α : Type u} {H : Hilbert α}
  {motive : (a : Formula α) → H ⊢! a → Sort u_1}
  (eaxm   : ∀ {φ}, (a : φ ∈ H.axioms) → motive φ ⟨eaxm a⟩)
  (mdp    : ∀ {φ ψ}, {hpq : H ⊢! (φ ➝ ψ)} → {hp : H ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (hpq ⨀ hp))
  (verum  : motive ⊤ verum!)
  (imply₁ : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ) imply₁!)
  (imply₂ : ∀ {φ ψ χ}, motive ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ) imply₂!)
  (and₁   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ φ) and₁!)
  (and₂   : ∀ {φ ψ},   motive (φ ⋏ ψ ➝ ψ) and₂!)
  (and₃   : ∀ {φ ψ},   motive (φ ➝ ψ ➝ φ ⋏ ψ) and₃!)
  (or₁    : ∀ {φ ψ},   motive (φ ➝ φ ⋎ ψ) or₁!)
  (or₂    : ∀ {φ ψ},   motive (ψ ➝ φ ⋎ ψ) or₂!)
  (or₃    : ∀ {φ ψ χ}, motive ((φ ➝ χ) ➝ (ψ ➝ χ) ➝ φ ⋎ ψ ➝ χ) or₃!)
  (neg_equiv : ∀ {φ}, motive (Axioms.NegEquiv φ) neg_equiv!) :
  {a : Formula α} → (t : H ⊢! a) → motive a t := by
  intro φ d;
  induction d.some with
  | eaxm h => exact eaxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop

end Deduction


open System

section

lemma weaker_than_of_subset_axiomset' {H₁ H₂ : Hilbert α} (hMaxm : ∀ {φ : Formula α}, φ ∈ H₁.axioms → H₂ ⊢! φ)
  : H₁ ≤ₛ H₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.rec! with
  | eaxm hp => apply hMaxm hp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => simp;

lemma weaker_than_of_subset_axiomset {H₁ H₂ : Hilbert α} (hSubset : H₁.axioms ⊆ H₂.axioms := by aesop) : H₁ ≤ₛ H₂ := by
  apply weaker_than_of_subset_axiomset';
  intro φ hp;
  apply eaxm! $ hSubset hp;

lemma Int_weaker_than_Cl : (Hilbert.Int α) ≤ₛ (Hilbert.Cl α) := weaker_than_of_subset_axiomset

lemma Int_weaker_than_KC : (Hilbert.Int α) ≤ₛ (Hilbert.KC α) := weaker_than_of_subset_axiomset

lemma Int_weaker_than_LC : (Hilbert.Int α) ≤ₛ (Hilbert.LC α) := weaker_than_of_subset_axiomset

lemma KC_weaker_than_Cl : (Hilbert.KC α) ≤ₛ (Hilbert.Cl α) := weaker_than_of_subset_axiomset' $ by
  rintro φ (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma LC_weaker_than_Cl [DecidableEq α] : (Hilbert.LC α) ≤ₛ (Hilbert.Cl α) := by
  apply weaker_than_of_subset_axiomset';
  rintro φ (⟨_, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

end


section Glivenko

theorem iff_provable_dn_efq_dne_provable [DecidableEq α] : (Hilbert.Int α) ⊢! ∼∼φ ↔ (Hilbert.Cl α) ⊢! φ := by
  constructor;
  . intro d; exact dne'! $ Int_weaker_than_Cl d;
  . intro d;
    induction d.some with
    | eaxm h =>
      simp at h;
      rcases h with (hEFQ | hLEM);
      . obtain ⟨ψ, hq⟩ := by simpa using hEFQ;
        subst hq;
        exact dni'! efq!;
      . obtain ⟨ψ, hq⟩ := by simpa using hLEM;
        subst hq;
        apply neg_equiv'!.mpr;
        apply FiniteContext.deduct'!;
        have : [∼(ψ ⋎ ∼ψ)] ⊢[Hilbert.Int α]! ∼ψ ⋏ ∼∼ψ := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | @mdp φ ψ h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq [DecidableEq α] : (Hilbert.Int α) ⊢! ∼φ ↔ (Hilbert.Cl α) ⊢! ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end Glivenko


end Hilbert

end LO.IntProp

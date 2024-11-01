import Foundation.Logic.HilbertStyle.Basic
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.IntProp.Formula

namespace LO.IntProp

variable {α : Type u}

structure Hilbert (α) where
  axiomSet : Theory α
notation "Ax(" Λ ")" => Hilbert.axiomSet Λ

namespace Hilbert

class IncludeEFQ (Λ : Hilbert α) where
  include_EFQ : 𝗘𝗙𝗤 ⊆ Ax(Λ) := by simp

class IncludeLEM (Λ : Hilbert α) where
  include_LEM : 𝗟𝗘𝗠 ⊆ Ax(Λ) := by simp

class IncludeDNE (Λ : Hilbert α) where
  include_DNE : 𝗗𝗡𝗘 ⊆ Ax(Λ) := by simp

end Hilbert

inductive Deduction (Λ : Hilbert α) : Formula α → Type _
  | eaxm {φ}     : φ ∈ Ax(Λ) → Deduction Λ φ
  | mdp {φ ψ}    : Deduction Λ (φ ➝ ψ) → Deduction Λ φ → Deduction Λ ψ
  | verum        : Deduction Λ $ ⊤
  | imply₁ φ ψ   : Deduction Λ $ φ ➝ ψ ➝ φ
  | imply₂ φ ψ χ : Deduction Λ $ (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | and₁ φ ψ     : Deduction Λ $ φ ⋏ ψ ➝ φ
  | and₂ φ ψ     : Deduction Λ $ φ ⋏ ψ ➝ ψ
  | and₃ φ ψ     : Deduction Λ $ φ ➝ ψ ➝ φ ⋏ ψ
  | or₁ φ ψ      : Deduction Λ $ φ ➝ φ ⋎ ψ
  | or₂ φ ψ      : Deduction Λ $ ψ ➝ φ ⋎ ψ
  | or₃ φ ψ χ    : Deduction Λ $ (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
  | neg_equiv φ  : Deduction Λ $ Axioms.NegEquiv φ

instance : System (Formula α) (Hilbert α) := ⟨Deduction⟩

open Deduction
open Hilbert

variable {Λ : Hilbert α}

instance : System.Minimal Λ where
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

instance [Λ.IncludeEFQ] : System.HasAxiomEFQ Λ where
  efq _ := eaxm $ Set.mem_of_subset_of_mem IncludeEFQ.include_EFQ (by simp);

instance [Λ.IncludeLEM] : System.HasAxiomLEM Λ where
  lem _ := eaxm $ Set.mem_of_subset_of_mem IncludeLEM.include_LEM (by simp);

instance [Λ.IncludeDNE] : System.HasAxiomDNE Λ where
  dne _ := eaxm $ Set.mem_of_subset_of_mem IncludeDNE.include_DNE (by simp);

instance [Λ.IncludeEFQ] : System.Intuitionistic Λ where

instance [Λ.IncludeDNE] : System.Classical Λ where

instance [DecidableEq α] [Λ.IncludeEFQ] [Λ.IncludeLEM] : System.Classical Λ where

lemma Deduction.eaxm! {Λ : Hilbert α} {φ : Formula α} (h : φ ∈ Ax(Λ)) : Λ ⊢! φ := ⟨eaxm h⟩


namespace Hilbert

abbrev theorems (Λ : Hilbert α) : Set (Formula α) := System.theory Λ

protected abbrev Minimal : Hilbert α := ⟨∅⟩

protected abbrev Intuitionistic : Hilbert α := ⟨𝗘𝗙𝗤⟩
notation "𝐈𝐧𝐭" => Hilbert.Intuitionistic
instance : IncludeEFQ (α := α) 𝐈𝐧𝐭 where
instance : System.Intuitionistic (𝐈𝐧𝐭 : Hilbert α) where

protected abbrev Classical : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗟𝗘𝗠⟩
notation "𝐂𝐥" => Hilbert.Classical
instance : IncludeLEM (α := α) 𝐂𝐥 where
instance : IncludeEFQ (α := α) 𝐂𝐥 where

-- `𝐊𝐂` from chagrov & zakharyaschev (1997)
protected abbrev KC : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗪𝗟𝗘𝗠⟩
notation "𝐊𝐂" => Hilbert.KC
instance : IncludeEFQ (α := α) 𝐊𝐂 where
instance : System.HasAxiomWeakLEM (𝐊𝐂 : Hilbert α) where
  wlem φ := by apply eaxm; aesop;

-- `𝐋𝐂` from chagrov & zakharyaschev (1997)
protected abbrev LC : Hilbert α := ⟨𝗘𝗙𝗤 ∪ 𝗗𝘂𝗺⟩
notation "𝐋𝐂" => Hilbert.LC
instance : IncludeEFQ (α := α) 𝐋𝐂 where
instance : System.HasAxiomDummett (𝐋𝐂 : Hilbert α) where
  dummett φ ψ := by apply eaxm; aesop;

/- MEMO:
  Term `WeakMinimal` and `WeakClassical` are from Ariola (2007)
  Minimal <ₛ WeakMinimal <ₛ WeakClassical <ₛ Classical
-/

protected abbrev WeakMinimal : Hilbert α := ⟨𝗟𝗘𝗠⟩

protected abbrev WeakClassical : Hilbert α := ⟨𝗣𝗲⟩


end Hilbert


namespace Deduction

variable {Λ : Hilbert α}

open System

noncomputable def rec! {α : Type u} {Λ : Hilbert α}
  {motive : (a : Formula α) → Λ ⊢! a → Sort u_1}
  (eaxm   : ∀ {φ}, (a : φ ∈ Ax(Λ)) → motive φ ⟨eaxm a⟩)
  (mdp    : ∀ {φ ψ}, {hpq : Λ ⊢! (φ ➝ ψ)} → {hp : Λ ⊢! φ} → motive (φ ➝ ψ) hpq → motive φ hp → motive ψ (hpq ⨀ hp))
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
  {a : Formula α} → (t : Λ ⊢! a) → motive a t := by
  intro φ d;
  induction d.some with
  | eaxm h => exact eaxm h
  | mdp hpq hp ihpq ihp => exact mdp (ihpq ⟨hpq⟩) (ihp ⟨hp⟩)
  | _ => aesop

end Deduction


open System

variable {Λ₁ Λ₂ : Hilbert α}

lemma weaker_than_of_subset_axiomset' (hMaxm : ∀ {φ : Formula α}, φ ∈ Ax(Λ₁) → Λ₂ ⊢! φ)
  : Λ₁ ≤ₛ Λ₂ := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  induction h using Deduction.rec! with
  | eaxm hp => apply hMaxm hp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => simp;

lemma weaker_than_of_subset_axiomset (hSubset : Ax(Λ₁) ⊆ Ax(Λ₂) := by aesop) : Λ₁ ≤ₛ Λ₂ := by
  apply weaker_than_of_subset_axiomset';
  intro φ hp;
  apply eaxm! $ hSubset hp;

lemma Int_weaker_than_Cl : (𝐈𝐧𝐭 : Hilbert α) ≤ₛ 𝐂𝐥 := weaker_than_of_subset_axiomset

lemma Int_weaker_than_KC : (𝐈𝐧𝐭 : Hilbert α) ≤ₛ 𝐊𝐂 := weaker_than_of_subset_axiomset

lemma Int_weaker_than_LC : (𝐈𝐧𝐭 : Hilbert α) ≤ₛ 𝐋𝐂 := weaker_than_of_subset_axiomset

lemma KC_weaker_than_Cl : (𝐊𝐂 : Hilbert α) ≤ₛ 𝐂𝐥 := by
  apply weaker_than_of_subset_axiomset';
  intro φ hp;
  rcases hp with (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> simp;

lemma LC_weaker_than_Cl [DecidableEq α] : (𝐋𝐂 : Hilbert α) ≤ₛ 𝐂𝐥 := by
  apply weaker_than_of_subset_axiomset';
  intro φ hp;
  rcases hp with (⟨_, rfl⟩ | ⟨_, _, rfl⟩) <;> simp;

variable {φ : Formula α}

theorem iff_provable_dn_efq_dne_provable [DecidableEq α] : 𝐈𝐧𝐭 ⊢! ∼∼φ ↔ 𝐂𝐥 ⊢! φ := by
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
        have : [∼(ψ ⋎ ∼ψ)] ⊢[𝐈𝐧𝐭]! ∼ψ ⋏ ∼∼ψ := demorgan₃'! $ FiniteContext.id!;
        exact neg_mdp! (and₂'! this) (and₁'! this);
    | @mdp φ ψ h₁ h₂ ih₁ ih₂ =>
      exact (dn_distribute_imply'! $ ih₁ ⟨h₁⟩) ⨀ ih₂ ⟨h₂⟩;
    | _ => apply dni'!; simp;

alias glivenko := iff_provable_dn_efq_dne_provable

theorem iff_provable_neg_efq_provable_neg_efq [DecidableEq α] : 𝐈𝐧𝐭 ⊢! ∼φ ↔ 𝐂𝐥 ⊢! ∼φ := by
  constructor;
  . intro d; exact glivenko.mp $ dni'! d;
  . intro d; exact tne'! $ glivenko.mpr d;

end LO.IntProp

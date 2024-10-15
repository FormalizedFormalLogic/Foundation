import Foundation.Logic.HilbertStyle.Supplemental

namespace LO

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [System F S]

namespace System

variable (𝓢 : S)

def ProvablyEquivalent (p q : F) : Prop := 𝓢 ⊢! p ⭤ q

local infix:45 " ≡ " => ProvablyEquivalent 𝓢

protected lemma ProvablyEquivalent.refl [System.Minimal 𝓢] (p : F) : p ≡ p := iff_id!

variable {𝓢}

protected lemma ProvablyEquivalent.symm [System.Minimal 𝓢] {p q : F} : p ≡ q → q ≡ p := iff_comm'!

protected lemma ProvablyEquivalent.trans [System.Minimal 𝓢] {p q r : F} : p ≡ q → q ≡ r → p ≡ r := iff_trans''!

lemma provable_iff_provablyEquivalent_verum [System.Minimal 𝓢] {p : F} : 𝓢 ⊢! p ↔ p ≡ ⊤ :=
  ⟨fun h ↦ iff_intro! imply_left_verum (dhyp! h), fun h ↦ (and_right! h) ⨀ verum!⟩

variable (𝓢)

def ProvablyEquivalent.setoid [System.Minimal 𝓢] : Setoid F where
  r := (· ≡ ·)
  iseqv := { refl := .refl _, symm := .symm, trans := .trans }

abbrev Lindenbaum [System.Minimal 𝓢] := Quotient (ProvablyEquivalent.setoid 𝓢)

namespace Lindenbaum

variable [System.Minimal 𝓢]

lemma of_eq_of {p q : F} : (⟦p⟧ : Lindenbaum 𝓢) = ⟦q⟧ ↔ p ≡ q := Quotient.eq (r := ProvablyEquivalent.setoid 𝓢)

instance : LE (Lindenbaum 𝓢) :=
  ⟨Quotient.lift₂ (fun p q ↦ 𝓢 ⊢! p ➝ q) fun p₁ q₁ p₂ q₂ hp hq ↦ by simp only [eq_iff_iff, imp_replace_iff!' hp hq]⟩

lemma le_def {p q : F} : (⟦p⟧ : Lindenbaum 𝓢) ≤ ⟦q⟧ ↔ 𝓢 ⊢! p ➝ q := iff_of_eq rfl

instance : Top (Lindenbaum 𝓢) := ⟨⟦⊤⟧⟩

instance : Bot (Lindenbaum 𝓢) := ⟨⟦⊥⟧⟩

instance : Inf (Lindenbaum 𝓢) := ⟨Quotient.lift₂ (fun p q ↦ ⟦p ⋏ q⟧) fun p₁ q₁ p₂ q₂ hp hq ↦ by
  simpa only [Quotient.eq] using and_replace_iff! hp hq⟩

instance : Sup (Lindenbaum 𝓢) := ⟨Quotient.lift₂ (fun p q ↦ ⟦p ⋎ q⟧) fun p₁ q₁ p₂ q₂ hp hq ↦ by
  simpa only [Quotient.eq] using or_replace_iff! hp hq⟩

instance : HImp (Lindenbaum 𝓢) := ⟨Quotient.lift₂ (fun p q ↦ ⟦p ➝ q⟧) fun p₁ q₁ p₂ q₂ hp hq ↦ by
  simpa only [Quotient.eq] using imp_replace_iff! hp hq⟩

instance : HasCompl (Lindenbaum 𝓢) := ⟨Quotient.lift (fun p ↦ ⟦∼p⟧) fun p₁ p₂ hp ↦ by
  simpa only [Quotient.eq] using neg_replace_iff'! hp⟩

lemma top_def : (⊤ : Lindenbaum 𝓢) = ⟦⊤⟧ := rfl

lemma bot_def : (⊥ : Lindenbaum 𝓢) = ⟦⊥⟧ := rfl

lemma inf_def (p q : F) : (⟦p⟧ : Lindenbaum 𝓢) ⊓ ⟦q⟧ = ⟦p ⋏ q⟧ := rfl

lemma sup_def (p q : F) : (⟦p⟧ : Lindenbaum 𝓢) ⊔ ⟦q⟧ = ⟦p ⋎ q⟧ := rfl

lemma himp_def (p q : F) : (⟦p⟧ : Lindenbaum 𝓢) ⇨ ⟦q⟧ = ⟦p ➝ q⟧ := rfl

lemma compl_def (p : F) : (⟦p⟧ : Lindenbaum 𝓢)ᶜ = ⟦∼p⟧ := rfl

instance : GeneralizedHeytingAlgebra (Lindenbaum 𝓢) where
  le_refl p := by
    induction' p using Quotient.ind with p
    simp [le_def]
  le_trans p q r := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    induction' r using Quotient.ind with r
    simp only [le_def]
    exact imp_trans''!
  le_antisymm p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    simp only [le_def, of_eq_of]
    intro hp hq; exact iff_intro! hp hq
  inf_le_left p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    simp only [inf_def, le_def]
    exact and₁!
  inf_le_right p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    simp only [inf_def, le_def]
    exact and₂!
  le_inf p q r := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    induction' r using Quotient.ind with r
    simp only [inf_def, le_def]
    exact imply_right_and!
  le_sup_left p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    simp only [sup_def, le_def]
    exact or₁!
  le_sup_right p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    simp only [sup_def, le_def]
    exact or₂!
  sup_le p q r := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    induction' r using Quotient.ind with r
    simp only [sup_def, le_def]
    exact or₃''!
  le_top p := by
    induction' p using Quotient.ind with p
    simp only [top_def, le_def]
    exact imply_left_verum
  le_himp_iff p q r := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    induction' r using Quotient.ind with r
    simp only [himp_def, le_def, inf_def]
    exact Iff.symm and_imply_iff_imply_imply'!

variable {𝓢}

lemma provable_iff_eq_top {p : F} : 𝓢 ⊢! p ↔ (⟦p⟧ : Lindenbaum 𝓢) = ⊤ := by
  simp [top_def, provable_iff_provablyEquivalent_verum]; rfl

lemma inconsistent_iff_trivial : Inconsistent 𝓢 ↔ (∀ p : Lindenbaum 𝓢, p = ⊤) := by
  simp [Inconsistent, provable_iff_eq_top]
  constructor
  · intro h p;
    induction p using Quotient.ind
    simp [h]
  · intro h f; simp [h]

lemma consistent_iff_nontrivial : Consistent 𝓢 ↔ Nontrivial (Lindenbaum 𝓢) := by
  apply not_iff_not.mp
  simp [not_consistent_iff_inconsistent, nontrivial_iff, inconsistent_iff_trivial]
  constructor
  · intro h p q; simp [h]
  · intro h p; exact h p ⊤

instance nontrivial_of_consistent [Consistent 𝓢] : Nontrivial (Lindenbaum 𝓢) := consistent_iff_nontrivial.mp inferInstance

end Lindenbaum

section intuitionistic

open Lindenbaum

variable [System.Intuitionistic 𝓢]

instance Lindenbaum.heyting : HeytingAlgebra (Lindenbaum 𝓢) where
  bot_le p := by
    induction' p using Quotient.ind with p
    simp only [bot_def, le_def]
    exact efq!
  himp_bot p := by
    induction' p using Quotient.ind with p
    simp [bot_def, himp_def, compl_def]
    exact iff_comm! ⨀ neg_equiv!

end intuitionistic

section classical

open Lindenbaum

variable [System.Classical 𝓢]

instance Lindenbaum.boolean : BooleanAlgebra (Lindenbaum 𝓢) where
  inf_compl_le_bot p := by
    induction' p using Quotient.ind with p
    simp only [compl_def, inf_def, bot_def, le_def, intro_bot_of_and!]
  top_le_sup_compl p := by
    induction' p using Quotient.ind with p
    simp [compl_def, sup_def, top_def, le_def]
    apply dhyp! lem!
  le_top p := by
    induction' p using Quotient.ind with p
    simp only [top_def, le_def]
    exact imply_left_verum
  bot_le p := by
    induction' p using Quotient.ind with p
    simp only [bot_def, le_def]
    exact efq!
  himp_eq p q := by
    induction' p using Quotient.ind with p
    induction' q using Quotient.ind with q
    rw [sup_comm]
    simp [himp_def, compl_def, sup_def]
    exact imply_iff_not_or!

end classical

end System

end LO

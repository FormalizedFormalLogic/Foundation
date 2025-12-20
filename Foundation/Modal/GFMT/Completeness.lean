import Foundation.Modal.GFMT.Basic
import Foundation.Modal.Entailment.K
import Foundation.Modal.Logic.Basic


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ ψ χ : F}

open Entailment

alias ruleI := C!_trans
alias ruleC := right_K!_intro
alias ruleD := left_A!_intro
alias orIntroL := or₁!
alias orIntroR := or₂!
alias andElimL := and₁!
alias andElimR := and₂!
alias impId := C!_id

lemma C_replace_both (h : 𝓢 ⊢ φ ➝ ψ) (h₁ : 𝓢 ⊢ φ' ➝ φ) (h₂ : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ' ➝ ψ' := C!_replace h₁ h₂ h
lemma collectOrAnd [DecidableEq F] : 𝓢 ⊢ ((φ ⋎ ψ) ⋏ (φ ⋎ χ)) ➝ (φ ⋎ (ψ ⋏ χ)) := by cl_prover;

lemma ruleD_fdisj' {Γ : Finset ι} (Φ : ι → F) (h : ∀ i ∈ Γ, 𝓢 ⊢ Φ i ➝ φ) : 𝓢 ⊢ (⩖ i ∈ Γ, Φ i) ➝ φ := by sorry;
lemma ruleC_fconj' {Γ : Finset ι} (Φ : ι → F) (h : ∀ i ∈ Γ, 𝓢 ⊢ φ ➝ Φ i) : 𝓢 ⊢ φ ➝ (⩕ i ∈ Γ, Φ i) := by sorry;
lemma mem_fdisj' {Γ : Finset ι} (Φ : ι → F) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ ψ ➝ ⩖ i ∈ Γ, Φ i := by sorry;
lemma mem_fconj' {Γ : Finset ι} (Φ : ι → F) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ (⩕ i ∈ Γ, Φ i) ➝ ψ := by sorry;

end LO.Entailment


namespace LO.Modal

open LO.Entailment
open Entailment

variable {L : Logic ℕ}

abbrev SubformulaOf (φ : Formula ℕ) : Type := { ψ // ψ ∈ φ.subformulas }
instance : Fintype (SubformulaOf φ) where
  elems := Finset.univ
  complete := by simp;


abbrev SubformulaSubsets (φ : Formula ℕ) := Finset (SubformulaOf φ)
abbrev HintikkaPair (φ : Formula ℕ) := (SubformulaSubsets φ) × (SubformulaSubsets φ)

namespace HintikkaPair

variable {H : HintikkaPair φ}

def Consistent (L : Logic ℕ) (H : HintikkaPair φ) : Prop := L ⊬ Finset.conj' H.1 (·.1) ➝ (⩖ x ∈ H.2, ↑x)
lemma iff_consistent : H.Consistent L ↔ ¬(L ⊢ Finset.conj' H.1 (·.1) ➝ (⩖ x ∈ H.2, ↑x)) := by simp [Consistent];
lemma iff_not_consistent : ¬(H.Consistent L) ↔ L ⊢ Finset.conj' H.1 (·.1) ➝ (⩖ x ∈ H.2, ↑x) := by simp [Consistent];

-- TOOD: code golf
@[simp]
lemma consistent_empty [Entailment.Cl L] [Entailment.Consistent L] : HintikkaPair.Consistent L (⟨∅, ∅⟩ : HintikkaPair φ) := by
  simp only [Consistent, Finset.conj'_empty, Finset.disj'_empty];
  by_contra hC;
  have := hC ⨀ verum!;
  obtain ⟨ψ, hψ⟩ := Entailment.Consistent.exists_unprovable (𝓢 := L) inferInstance;
  apply hψ;
  apply of_O!;
  assumption;

@[grind]
def Saturated (H : HintikkaPair φ) := H.1 ∪ H.2 = Finset.univ

@[grind →]
lemma mem₁_of_not_mem₂_of_saturated (h : H.Saturated) : ψ ∉ H.2 → ψ ∈ H.1 := by
  have := Finset.ext_iff.mp h ψ;
  grind;

@[grind →]
lemma mem₂_of_not_mem₁_of_saturated (h : H.Saturated) : ψ ∉ H.1 → ψ ∈ H.2 := by
  have := Finset.ext_iff.mp h ψ;
  grind;

def insert₁ (H : HintikkaPair φ) (ψ : { ψ // ψ ∈ φ.subformulas }) : HintikkaPair φ := ⟨insert ψ H.1, H.2⟩
def insert₂ (H : HintikkaPair φ) (ψ : { ψ // ψ ∈ φ.subformulas }) : HintikkaPair φ := ⟨H.1, insert ψ H.2⟩

variable [Entailment.Cl L]

@[grind ⇒]
lemma either_consistent_insert
  (H_consis : H.Consistent L) (ψ)
  : Consistent L (H.insert₁ ψ) ∨ Consistent L (H.insert₂ ψ) := by
  contrapose! H_consis;
  apply iff_not_consistent.mpr;

  obtain ⟨h₁, h₂⟩ := H_consis;

  let Γ₀ : Formula ℕ := ⩕ γ ∈ H.1, ↑γ;
  let Γ₁ : Formula ℕ := ⩕ γ ∈ (H.insert₁ ψ).1, ↑γ;

  let Δ₀ : Formula ℕ := ⩖ δ ∈ H.2, ↑δ;
  let Δ₁ : Formula ℕ := ⩖ δ ∈ (H.insert₂ ψ).2, ↑δ;

  replace h₁ : L ⊢ Γ₁ ➝ Δ₀ := iff_not_consistent.mp h₁;
  replace h₂ : L ⊢ Γ₀ ➝ Δ₁ := iff_not_consistent.mp h₂;
  show L ⊢ Γ₀ ➝ Δ₀;

  apply C!_trans ?_ $ ruleD impId h₁;
  show L ⊢ Γ₀ ➝ Δ₀ ⋎ Γ₁;

  apply ruleI $ ruleC h₂ orIntroR;
  show L ⊢ Δ₁ ⋏ (Δ₀ ⋎ Γ₀) ➝ Δ₀ ⋎ Γ₁;

  apply C_replace_both;
  . show L ⊢ (Δ₀ ⋎ ↑ψ) ⋏ (Δ₀ ⋎ Γ₀) ➝ Δ₀ ⋎ ↑ψ ⋏ Γ₀;
    exact collectOrAnd;
  . apply ruleC ?_ andElimR;
    apply ruleI andElimL;
    apply ruleD_fdisj';
    simp only [insert₂, Finset.mem_insert, forall_eq_or_imp];
    constructor;
    . exact orIntroR;
    . intro δ hδ;
      apply ruleI ?_ orIntroL;
      apply mem_fdisj';
      grind;
  . show L ⊢ Δ₀ ⋎ ↑ψ ⋏ Γ₀ ➝ Δ₀ ⋎ Γ₁;
    apply ruleD orIntroL;
    apply ruleI ?_ orIntroR;
    apply ruleC_fconj';
    simp only [insert₁, Finset.mem_insert, forall_eq_or_imp];
    constructor;
    . exact andElimL;
    . intro γ hγ;
      apply ruleI andElimR;
      apply mem_fconj';
      grind;

namespace lindenbaum

open Classical

variable {L : Logic ℕ} {φ ψ} {H : HintikkaPair φ}

noncomputable def next (L : Logic ℕ) (ψ : SubformulaOf φ) (H : HintikkaPair φ) : HintikkaPair φ :=
  if Consistent L (H.insert₁ ψ) then H.insert₁ ψ else H.insert₂ ψ

variable [Entailment.Cl L]

lemma next_consistent (H_consis : H.Consistent L) : (next L ψ H).Consistent L := by
  by_cases h : Consistent L (H.insert₁ ψ) <;>
  . dsimp [next, h];
    grind;

lemma next_monotone₁ : H.1 ⊆ (next L ψ H).1 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

lemma next_monotone₂ : H.2 ⊆ (next L ψ H).2 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

lemma next_either_mem (ψ) : ψ ∈ (next L ψ H).1 ∨ ψ ∈ (next L ψ H).2 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

noncomputable def enum (L : Logic ℕ) (H : HintikkaPair φ) : List (SubformulaOf φ) → HintikkaPair φ
  | [] => H
  | ψ :: Δ => next L ψ (enum L H Δ)

lemma enum_consistent (H_consis : H.Consistent L) (Γ : List (SubformulaOf φ)) : (enum L H Γ).Consistent L := by
  induction Γ with
  | nil => assumption;
  | cons ψ Γ ih => apply next_consistent; exact ih;

lemma enum_monotone₁ {Γ : List (SubformulaOf φ)} : H.1 ⊆ (enum L H Γ).1 := by
  induction Γ with
  | nil => simp [enum];
  | cons ψ Γ ih =>
    trans (enum L H Γ).1;
    . exact ih;
    . apply next_monotone₁

lemma enum_monotone₂ {Γ : List (SubformulaOf φ)} : H.2 ⊆ (enum L H Γ).2 := by
  induction Γ with
  | nil => simp [enum];
  | cons ψ Γ ih =>
    trans (enum L H Γ).2;
    . exact ih;
    . apply next_monotone₂

lemma enum_of_mem (hψ : ψ ∈ Γ) : ψ ∈ (enum L H Γ).1 ∨ ψ ∈ (enum L H Γ).2 := by
  induction Γ with
  | nil => simp at hψ;
  | cons χ Δ ih =>
    simp only [List.mem_cons] at hψ;
    rcases hψ with rfl | hψ;
    . rcases next_either_mem (L := L) (H := enum L H Δ) ψ with h | h;
      . left; simpa [enum];
      . right; simpa [enum];
    . rcases ih hψ with h | h;
      . left; apply next_monotone₁ h;
      . right; apply next_monotone₂ h;

noncomputable def sat (L : Logic ℕ) (H : HintikkaPair φ) : HintikkaPair φ := enum L H Finset.univ.toList

lemma sat_saturated : (sat L H).Saturated := by
  ext ψ;
  simp only [Finset.univ_eq_attach, Finset.mem_union, Finset.mem_attach, iff_true];
  apply enum_of_mem;
  simp;

end lindenbaum

open lindenbaum in
lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent L) : ∃ H' : HintikkaPair φ, H.1 ⊆ H'.1 ∧ H.2 ⊆ H'.2 ∧ H'.Consistent L ∧ H'.Saturated := by
  use lindenbaum.sat L H;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply enum_monotone₁;
  . apply enum_monotone₂;
  . apply enum_consistent H_consis;
  . apply sat_saturated;

end HintikkaPair

abbrev ConsistentSaturatedHintikkaPair (L) (φ) := { H : HintikkaPair φ // H.Consistent L ∧ H.Saturated }

namespace ConsistentSaturatedHintikkaPair

variable {H : ConsistentSaturatedHintikkaPair L φ}

open Formula

variable [Entailment.Cl L]

lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent L) : ∃ H' : ConsistentSaturatedHintikkaPair L φ, H.1 ⊆ H'.1.1 ∧ H.2 ⊆ H'.1.2 := by
  obtain ⟨H', _, _, H'_consis, H'_saturated⟩ := HintikkaPair.lindenbaum H H_consis;
  use ⟨H', ⟨H'_consis, H'_saturated⟩⟩;

@[simp, grind .] lemma consistent (H : ConsistentSaturatedHintikkaPair L φ) : HintikkaPair.Consistent L H.1 := H.2.1
@[simp, grind .] lemma saturated (H : ConsistentSaturatedHintikkaPair L φ) : HintikkaPair.Saturated H.1 := H.2.2

noncomputable instance [Entailment.Consistent L] : Nonempty (ConsistentSaturatedHintikkaPair L φ) := ⟨lindenbaum (H := ⟨∅, ∅⟩) (HintikkaPair.consistent_empty) |>.choose⟩

@[grind .]
lemma not_mem_both : ¬(ψ ∈ H.1.1 ∧ ψ ∈ H.1.2) := by
  by_contra! hC;
  obtain ⟨h₁, h₂⟩ := hC;
  apply H.consistent;
  apply C_replace_both;
  . show L ⊢ ψ.1 ➝ ψ.1;
    exact impId;
  . apply mem_fconj';
    grind;
  . apply mem_fdisj';
    grind;

@[grind =]
lemma iff_mem₁_not_mem₂ : ψ ∈ H.1.1 ↔ ψ ∉ H.1.2 := by
  constructor;
  . by_contra! hC;
    apply not_mem_both hC;
  . apply HintikkaPair.mem₁_of_not_mem₂_of_saturated H.saturated;

@[grind =]
lemma iff_mem₂_not_mem₁ : ψ ∈ H.1.2 ↔ ψ ∉ H.1.1 := by
  constructor;
  . by_contra! hC;
    apply not_mem_both hC.symm;
  . apply HintikkaPair.mem₂_of_not_mem₁_of_saturated H.saturated;



lemma imp_closed (hSψ : ψ ∈ φ.subformulas) (hSχ : χ ∈ φ.subformulas) : L ⊢ ψ ➝ χ → ⟨ψ, hSψ⟩ ∈ H.1.1 → ⟨χ, hSχ⟩ ∈ H.1.1 := by
  rintro h₁ hφ;
  by_contra hψ;
  replace hψ := iff_mem₂_not_mem₁.mpr hψ;
  apply H.consistent;
  apply C_replace_both h₁;
  . apply mem_fconj'; grind;
  . apply mem_fdisj'; grind;

@[simp, grind =>]
lemma no_bot (h : ⊥ ∈ φ.subformulas) : ⟨⊥, h⟩ ∉ H.1.1 := by
  by_contra hC;
  apply H.consistent;
  apply ruleI (ψ := ⊥);
  . apply mem_fconj';
    grind;
  . exact efq!;

@[simp, grind =>]
lemma mem_top (h : ⊤ ∈ φ.subformulas) : ⟨⊤, h⟩ ∈ H.1.1 := by
  apply iff_mem₁_not_mem₂.mpr;
  by_contra hC;
  apply H.consistent;
  apply ruleI (ψ := ⊤);
  . sorry;
  . apply mem_fdisj';
    grind;

lemma iff_mem_and (hSub : ψ ⋏ χ ∈ φ.subformulas) : ⟨ψ ⋏ χ, hSub⟩ ∈ H.1.1 ↔ ⟨ψ, subformulas.mem_and hSub |>.1⟩ ∈ H.1.1 ∧ ⟨χ, subformulas.mem_and hSub |>.2⟩ ∈ H.1.1 := by
  constructor;
  . rintro h;
    constructor;
    . apply imp_closed ?_ ?_ andElimL h <;> grind;
    . apply imp_closed ?_ ?_ andElimR h <;> grind;
  . rintro ⟨hψ, hχ⟩;
    by_contra hψχ;
    replace hψχ := iff_mem₂_not_mem₁.mpr hψχ;
    apply H.consistent;
    apply C_replace_both;
    . show L ⊢ ψ ⋏ χ ➝ ψ ⋏ χ;
      exact impId;
    . apply ruleC <;>
      . apply mem_fconj';
        grind;
    . apply mem_fdisj';
      grind;

lemma iff_mem_or (hSub : ψ ⋎ χ ∈ φ.subformulas) : ⟨ψ ⋎ χ, hSub⟩ ∈ H.1.1 ↔ ⟨ψ, subformulas.mem_or hSub |>.1⟩ ∈ H.1.1 ∨ ⟨χ, subformulas.mem_or hSub |>.2⟩ ∈ H.1.1 := by
  constructor;
  . rintro h;
    by_contra! hC;
    obtain ⟨hφ, hψ⟩ := hC;
    replace hφ := iff_mem₂_not_mem₁.mpr hφ;
    replace hψ := iff_mem₂_not_mem₁.mpr hψ;
    apply H.consistent;
    apply C_replace_both;
    . show L ⊢ ψ ⋎ χ ➝ ψ ⋎ χ;
      exact impId;
    . apply mem_fconj';
      grind;
    . apply ruleD <;>
      . apply mem_fdisj';
        grind;
  . rintro (hφ | hψ);
    . apply imp_closed ?_ ?_ orIntroL hφ <;> grind;
    . apply imp_closed ?_ ?_ orIntroR hψ <;> grind;

lemma iff_mem_imp (hSub : ψ ➝ χ ∈ φ.subformulas) : ⟨ψ ➝ χ, hSub⟩ ∈ H.1.1 ↔ (⟨ψ, subformulas.mem_imp hSub |>.1⟩ ∈ H.1.1 → ⟨χ, subformulas.mem_imp hSub |>.2⟩ ∈ H.1.1) := by
  constructor;
  . intro h₁ h₂;
    sorry;
  . rintro hφ;
    apply imp_closed (ψ := χ) ?_ ?_ ?_ ?_;
    . grind;
    . grind;
    . cl_prover;
    . apply hφ;
      sorry;

end ConsistentSaturatedHintikkaPair


namespace GFMT

open Formula

variable [Entailment.Cl L] [Entailment.Consistent L]

open Classical in
noncomputable def hintikkaModel
  (L : Logic ℕ) [Entailment.Cl L] [Entailment.Consistent L]
  (φ : Formula ℕ) (Φ : Formula ℕ → Set (Formula ℕ)) : GFMT.Model where
  World := ConsistentSaturatedHintikkaPair L φ
  Rel {ψ H I} := ∀ χ, ψ ∈ Φ χ → ∀ {_ : □χ ∈ φ.subformulas}, ⟨□χ, by grind⟩ ∈ H.1.1 → ⟨χ, by grind⟩ ∈ I.1.1
  Phi := Φ
  Valuation H a := ∀ {_ : ((.atom a) ∈ φ.subformulas)}, ⟨(.atom a), by grind⟩ ∈ H.1.1

open Formula.GFMT in
open ConsistentSaturatedHintikkaPair in
lemma hintikkaModel.truthlemma {H : (hintikkaModel L φ Φ).World} (hψ : ψ ∈ φ.subformulas) : ⟨ψ, hψ⟩ ∈ H.1.1 ↔ H ⊩ ψ := by
  induction ψ generalizing H with
  | hfalsum => simp;
  | hatom => tauto;
  | himp ψ χ ihψ ihχ =>
    replace ihψ := @ihψ H (by grind);
    replace ihχ := @ihχ H (by grind);
    constructor;
    . intro h hψ;
      apply ihχ.mp;
      sorry;
    . intro h;
      sorry;
  | hbox ψ ih =>
    constructor;
    . intro h χ hχ I RHI;
      apply ih (by grind) |>.mp;
      apply @RHI ψ hχ hψ h;
    . contrapose!;
      intro h;
      apply Forces.not_box_def.mpr;
      use ψ;
      constructor;
      . sorry;
      . obtain ⟨I, hI₁, hI₂⟩ := lindenbaum (H := H.1) (H_consis := H.consistent);
        use I;
        constructor;
        . intro χ hχ _ a;
          sorry;
        . apply @ih I (by grind) |>.not.mp;
          sorry;

end GFMT


end LO.Modal

module

public import Foundation.Propositional.FMT.Hilbert.Basic
public import Foundation.Propositional.Hilbert.WF_VF

@[expose] public section

namespace LO.Propositional

open Entailment.Corsi

variable {S} [Entailment S (Formula ℕ)]
         {𝓢 : S}

abbrev SubformulaOf (φ : Formula ℕ) : Type := { ψ // ψ ∈ φ.subformulas }
instance : Fintype (SubformulaOf φ) where
  elems := Finset.univ
  complete := by simp;


abbrev SubformulaSubsets (φ : Formula ℕ) := Finset (SubformulaOf φ)
abbrev HintikkaPair (φ : Formula ℕ) := (SubformulaSubsets φ) × (SubformulaSubsets φ)

namespace HintikkaPair

variable {H : HintikkaPair φ}

def Consistent (𝓢 : S) (H : HintikkaPair φ) : Prop := 𝓢 ⊬ (⩕ x ∈ H.1, ↑x) 🡒 (⩖ x ∈ H.2, ↑x)
lemma iff_consistent : H.Consistent 𝓢 ↔ (𝓢 ⊬ (⩕ x ∈ H.1, ↑x) 🡒 (⩖ x ∈ H.2, ↑x)) := by simp [Consistent];
lemma iff_not_consistent : ¬(H.Consistent 𝓢) ↔ 𝓢 ⊢ (⩕ x ∈ H.1, ↑x) 🡒 (⩖ x ∈ H.2, ↑x) := by simp [Consistent];

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

variable [Entailment.VF 𝓢]

@[grind ⇒]
lemma either_consistent_insert
  (H_consis : H.Consistent 𝓢) (ψ)
  : Consistent 𝓢 (H.insert₁ ψ) ∨ Consistent 𝓢 (H.insert₂ ψ) := by
  contrapose! H_consis;
  apply iff_not_consistent.mpr;

  obtain ⟨h₁, h₂⟩ := H_consis;

  let Γ₀ : Formula ℕ := ⩕ γ ∈ H.1, ↑γ;
  let Γ₁ : Formula ℕ := ⩕ γ ∈ (H.insert₁ ψ).1, ↑γ;

  let Δ₀ : Formula ℕ := ⩖ δ ∈ H.2, ↑δ;
  let Δ₁ : Formula ℕ := ⩖ δ ∈ (H.insert₂ ψ).2, ↑δ;

  replace h₁ : 𝓢 ⊢ Γ₁ 🡒 Δ₀ := iff_not_consistent.mp h₁;
  replace h₂ : 𝓢 ⊢ Γ₀ 🡒 Δ₁ := iff_not_consistent.mp h₂;
  show 𝓢 ⊢ Γ₀ 🡒 Δ₀;

  apply ruleI ?_ $ ruleD impId h₁;
  show 𝓢 ⊢ Γ₀ 🡒 Δ₀ ⋎ Γ₁;

  apply ruleI $ ruleC h₂ orIntroR;
  show 𝓢 ⊢ Δ₁ ⋏ (Δ₀ ⋎ Γ₀) 🡒 Δ₀ ⋎ Γ₁;

  apply C_replace_both;
  . show 𝓢 ⊢ (Δ₀ ⋎ ↑ψ) ⋏ (Δ₀ ⋎ Γ₀) 🡒 Δ₀ ⋎ ↑ψ ⋏ Γ₀;
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
  . apply ruleD orIntroL;
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

variable {𝓢 : S} {φ : Formula ℕ} {H : HintikkaPair φ}

noncomputable def next (𝓢 : S) (ψ : SubformulaOf φ) (H : HintikkaPair φ) : HintikkaPair φ :=
  if Consistent 𝓢 (H.insert₁ ψ) then H.insert₁ ψ else H.insert₂ ψ

variable [Entailment.VF 𝓢] in
lemma next_consistent (H_consis : H.Consistent 𝓢) : (next 𝓢 ψ H).Consistent 𝓢 := by
  by_cases h : Consistent 𝓢 (H.insert₁ ψ) <;>
  . dsimp [next, h];
    grind;

lemma next_monotone₁ : H.1 ⊆ (next 𝓢 ψ H).1 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

lemma next_monotone₂ : H.2 ⊆ (next 𝓢 ψ H).2 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

lemma next_either_mem (ψ) : ψ ∈ (next 𝓢 ψ H).1 ∨ ψ ∈ (next 𝓢 ψ H).2 := by
  simp [next, insert₁, insert₂];
  split <;> grind;

noncomputable def enum (𝓢 : S) (H : HintikkaPair φ) : List (SubformulaOf φ) → HintikkaPair φ
  | [] => H
  | ψ :: Δ => next 𝓢 ψ (enum 𝓢 H Δ)

variable [Entailment.VF 𝓢] in
lemma enum_consistent (H_consis : H.Consistent 𝓢) (Γ : List (SubformulaOf φ)) : (enum 𝓢 H Γ).Consistent 𝓢 := by
  induction Γ with
  | nil => assumption;
  | cons ψ Γ ih => apply next_consistent; exact ih;

lemma enum_monotone₁ {Γ : List (SubformulaOf φ)} : H.1 ⊆ (enum 𝓢 H Γ).1 := by
  induction Γ with
  | nil => simp [enum];
  | cons ψ Γ ih =>
    trans (enum 𝓢 H Γ).1;
    . exact ih;
    . apply next_monotone₁

lemma enum_monotone₂ {Γ : List (SubformulaOf φ)} : H.2 ⊆ (enum 𝓢 H Γ).2 := by
  induction Γ with
  | nil => simp [enum];
  | cons ψ Γ ih =>
    trans (enum 𝓢 H Γ).2;
    . exact ih;
    . apply next_monotone₂

lemma enum_of_mem (hψ : ψ ∈ Γ) : ψ ∈ (enum 𝓢 H Γ).1 ∨ ψ ∈ (enum 𝓢 H Γ).2 := by
  induction Γ with
  | nil => simp at hψ;
  | cons χ Δ ih =>
    simp only [List.mem_cons] at hψ;
    rcases hψ with rfl | hψ;
    . rcases next_either_mem (𝓢 := 𝓢) (H := enum 𝓢 H Δ) ψ with h | h;
      . left; simpa [enum];
      . right; simpa [enum];
    . rcases ih hψ with h | h;
      . left; apply next_monotone₁ h;
      . right; apply next_monotone₂ h;

noncomputable def sat (𝓢 : S) (H : HintikkaPair φ) : HintikkaPair φ := enum 𝓢 H Finset.univ.toList

lemma sat_saturated : (sat 𝓢 H).Saturated := by
  ext ψ;
  simp only [Finset.mem_union, Finset.mem_univ, iff_true];
  apply enum_of_mem;
  simp;

end lindenbaum

open lindenbaum in
lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent 𝓢) : ∃ H' : HintikkaPair φ, H.1 ⊆ H'.1 ∧ H.2 ⊆ H'.2 ∧ H'.Consistent 𝓢 ∧ H'.Saturated := by
  use lindenbaum.sat 𝓢 H;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . apply enum_monotone₁;
  . apply enum_monotone₂;
  . apply enum_consistent H_consis;
  . apply sat_saturated;

end HintikkaPair

abbrev ConsistentSaturatedHintikkaPair (𝓢 : S) (φ) := { H : HintikkaPair φ // H.Consistent 𝓢 ∧ H.Saturated }

namespace ConsistentSaturatedHintikkaPair

variable {H : ConsistentSaturatedHintikkaPair 𝓢 φ}

open Formula

variable [Entailment.VF 𝓢] in
lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent 𝓢) : ∃ H' : ConsistentSaturatedHintikkaPair 𝓢 φ, H.1 ⊆ H'.1.1 ∧ H.2 ⊆ H'.1.2 := by
  obtain ⟨H', _, _, H'_consis, H'_saturated⟩ := HintikkaPair.lindenbaum H H_consis;
  use ⟨H', ⟨H'_consis, H'_saturated⟩⟩;

@[simp, grind .] lemma consistent (H : ConsistentSaturatedHintikkaPair 𝓢 φ) : HintikkaPair.Consistent 𝓢 H.1 := H.2.1
@[simp, grind .] lemma saturated (H : ConsistentSaturatedHintikkaPair 𝓢 φ) : HintikkaPair.Saturated H.1 := H.2.2

variable [Entailment.VF 𝓢]

@[grind .]
lemma not_mem_both : ¬(ψ ∈ H.1.1 ∧ ψ ∈ H.1.2) := by
  by_contra! hC;
  rcases hC with ⟨h₁, h₂⟩;
  apply H.consistent;
  apply C_replace_both;
  . show 𝓢 ⊢ ψ.1 🡒 ψ.1;
    exact impId;
  . apply mem_fconj'; grind;
  . apply mem_fdisj'; grind;

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

lemma imp_closed (hSψ : ψ ∈ φ.subformulas) (hSχ : χ ∈ φ.subformulas) : 𝓢 ⊢ ψ 🡒 χ → ⟨ψ, hSψ⟩ ∈ H.1.1 → ⟨χ, hSχ⟩ ∈ H.1.1 := by
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
  . exact efq;

@[simp, grind =>]
lemma mem_top (h : ⊤ ∈ φ.subformulas) : ⟨⊤, h⟩ ∈ H.1.1 := by
  apply iff_mem₁_not_mem₂.mpr;
  by_contra hC;
  apply H.consistent;
  apply ruleI (ψ := ⊤);
  . apply af; simp;
  . apply mem_fdisj'; grind;

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
    . show 𝓢 ⊢ ψ ⋏ χ 🡒 ψ ⋏ χ;
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
    . show 𝓢 ⊢ ψ ⋎ χ 🡒 ψ ⋎ χ;
      exact impId;
    . apply mem_fconj';
      grind;
    . apply ruleD <;>
      . apply mem_fdisj';
        grind;
  . rintro (hφ | hψ);
    . apply imp_closed ?_ ?_ orIntroL hφ <;> grind;
    . apply imp_closed ?_ ?_ orIntroR hψ <;> grind;

end ConsistentSaturatedHintikkaPair


namespace FMT

open Formula

variable [Entailment.VF 𝓢] [Entailment.Disjunctive 𝓢] [Entailment.Consistent 𝓢]

open Classical in
noncomputable def HintikkaModel (𝓢 : S) [Entailment.VF 𝓢] [Entailment.Consistent 𝓢] [Entailment.Disjunctive 𝓢] (φ : Formula ℕ) : FMT.Model :=
  letI H₀ : HintikkaPair φ := ⟨
    ∅,
    Finset.univ.filter (λ ⟨δ, hδ⟩ => ∃ χ ξ, δ = χ.1 🡒 ξ.1 ∧ ∃ H : ConsistentSaturatedHintikkaPair 𝓢 φ, χ ∈ H.1.1 ∧ ξ ∈ H.1.2 )
  ⟩;
  haveI hH₀ := ConsistentSaturatedHintikkaPair.lindenbaum H₀ $ by
    show H₀.Consistent 𝓢;
    apply HintikkaPair.iff_consistent.mpr;
    by_contra! hC;
    have : 𝓢 ⊢ ⩖ δ ∈ H₀.2, ↑δ := hC ⨀ by simp [H₀];
    obtain ⟨δ, hδ₁, hδ₂⟩ : ∃ δ ∈ H₀.2, 𝓢 ⊢ ↑δ := by
      apply DP_fdisj;
      apply Entailment.mdp! hC;
      simp [H₀];
    obtain ⟨χ, ξ, e, Γ, hΓχ, hΓξ⟩ : ∃ χ ξ : SubformulaOf φ, δ = χ.1 🡒 ξ.1 ∧ ∃ H : ConsistentSaturatedHintikkaPair 𝓢 φ, χ ∈ H.1.1 ∧ ξ ∈ H.1.2  := by
      simpa [H₀] using hδ₁;
    apply Γ.consistent;
    apply C_replace_both;
    . show 𝓢 ⊢ χ.1 🡒 ξ.1;
      exact e ▸ hδ₂;
    . apply mem_fconj';
      use χ;
    . apply mem_fdisj';
      use ξ;
  {
    World := ConsistentSaturatedHintikkaPair 𝓢 φ
    Rel ψ H I :=
      match ψ with
      | χ 🡒 ξ =>
        ∀ (h : χ 🡒 ξ ∈ φ.subformulas),
          ⟨χ 🡒 ξ, h⟩ ∈ H.1.2 ∨
          ⟨χ, Formula.subformulas.mem_imp h |>.1⟩ ∈ I.1.2 ∨
          ⟨ξ, Formula.subformulas.mem_imp h |>.2⟩ ∈ I.1.1
      | _ => True
    root := hH₀.choose
    rooted {ψ I} := by
      match ψ with
      | χ 🡒 ξ =>
        simp only;
        rintro _;
        let χ' : SubformulaOf φ := ⟨χ, by grind⟩;
        let ξ' : SubformulaOf φ := ⟨ξ, by grind⟩;
        by_cases h : ∀ I : ConsistentSaturatedHintikkaPair 𝓢 φ, χ' ∈ I.1.2 ∨ ξ' ∈ I.1.1;
        . right;
          exact h I;
        . left;
          apply hH₀.choose_spec |>.2;
          suffices ∃ χ' ξ', χ 🡒 ξ = χ'.1 🡒 ξ'.1 ∧ ∃ I : ConsistentSaturatedHintikkaPair 𝓢 φ, χ' ∈ I.1.1 ∧ ξ' ∈ I.1.2 by
            simpa [H₀] using this;
          push Not at h;
          obtain ⟨I, hI₁, hI₂⟩ := h;
          use χ', ξ';
          refine ⟨?_, I, ?_, ?_⟩;
          . rfl;
          . apply ConsistentSaturatedHintikkaPair.iff_mem₁_not_mem₂.mpr hI₁;
          . apply ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mpr hI₂;
      | χ ⋏ ξ | χ ⋎ ξ | ⊥ | #a => tauto;
    Val a H := (ha : #a ∈ φ.subformulas) → ⟨#a, ha⟩ ∈ H.1.1
  }

open Formula.FMT in
lemma HintikkaModel.truthlemma {H : HintikkaModel 𝓢 φ} (hsub : ψ ∈ φ.subformulas) : ⟨ψ, hsub⟩ ∈ H.1.1 ↔ H ⊩ ψ := by
  induction ψ generalizing H with
  | hatom a => tauto;
  | hfalsum => simp;
  | hand => apply Iff.trans $ ConsistentSaturatedHintikkaPair.iff_mem_and hsub; grind;
  | hor => apply Iff.trans $ ConsistentSaturatedHintikkaPair.iff_mem_or hsub; grind;
  | himp χ ξ ihχ ihξ =>
    constructor;
    . intro hχξ₁ I RHI hχ₁;
      replace hχ₁ := ihχ (by grind) |>.mpr hχ₁;
      rcases RHI hsub with (hχξ₂ | hχ₂ | hξ₁);
      . grind;
      . grind;
      . apply ihξ _ |>.mp hξ₁;
    . contrapose!;
      intro h;
      apply Forces.not_def_imp.mpr;
      obtain ⟨I, hI₁, hI₂⟩ := ConsistentSaturatedHintikkaPair.lindenbaum (φ := φ) ({⟨χ, by grind⟩}, {⟨ξ, by grind⟩}) $ by
        show HintikkaPair.Consistent 𝓢 ({⟨χ, _⟩}, {⟨ξ, _⟩});
        suffices 𝓢 ⊬ χ 🡒 ξ by simpa [HintikkaPair.Consistent];
        by_contra! hC;
        apply H.consistent;
        apply af;
        apply ?_ ⨀ hC;
        apply mem_fdisj';
        replace h := ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mpr h;
        use ⟨χ 🡒 ξ, by tauto⟩;
      use I;
      refine ⟨?_, ?_, ?_⟩;
      . dsimp [HintikkaModel]; grind;
      . apply ihχ (by grind) |>.mp; grind;
      . apply ihξ (by grind) |>.not.mp; grind;


open Formula.FMT in
theorem provable_of_validOnHintikkaModel : (HintikkaModel 𝓢 φ) ⊧ φ → 𝓢 ⊢ φ := by
  contrapose!;
  intro h;
  apply ValidOnModel.not_of_exists_world;
  obtain ⟨H, _, hH₂⟩ := ConsistentSaturatedHintikkaPair.lindenbaum ⟨∅, {⟨φ, subformulas.mem_self⟩}⟩ $ by
    show HintikkaPair.Consistent 𝓢 (∅, {⟨φ, _⟩});
    suffices ¬𝓢 ⊢ ⊤ 🡒 φ by simpa [HintikkaPair.Consistent];
    contrapose! h;
    exact h ⨀ Entailment.verum!;
  use H;
  apply HintikkaModel.truthlemma (by grind) |>.not.mp;
  apply ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mp;
  apply hH₂;
  simp;

end FMT


end LO.Propositional
end

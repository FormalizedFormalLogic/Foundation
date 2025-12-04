import Foundation.Propositional.FMT.Hilbert
import Foundation.Propositional.Hilbert.WF_VF

namespace LO.Propositional


namespace Entailment.Corsi

variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

variable [DecidableEq α]
variable [Entailment.VF 𝓢]

variable {φ ψ χ γ δ : Formula α}

lemma insert_LConj {Γ : List (Formula α)} : 𝓢 ⊢ φ ⋏ Γ.conj₂ ➝ (φ :: Γ).conj₂ := by
  match Γ with
  | [] => simp [List.conj₂];
  | γ :: Γ => apply ruleC andElimL andElimR;

@[simp, grind .]
lemma conjconj {Γ : Finset (Formula α)} : 𝓢 ⊢ (Γ.conj) ➝ Γ.toList.conj₂ := by simp [Finset.conj];

lemma C_replace_both (h : 𝓢 ⊢ φ ➝ ψ) (h₁ : 𝓢 ⊢ φ' ➝ φ) (h₂ : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ' ➝ ψ' := by
  apply C_trans h₁;
  apply C_trans ?_ h₂;
  apply h;

@[grind <=]
lemma CKK_right_replace (h : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋏ ψ ➝ φ ⋏ ψ' := by
  apply ruleC;
  . simp;
  . apply C_trans ?_ h;
    simp;

lemma mem_lconj₂ {Γ : List (Formula α)} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    rcases h with rfl | h;
    . simp;
    . apply C_trans ?_ $ ih h;
      simp;
  | _ => simp_all;

lemma FConj_of_mem {Γ : Finset (Formula α)} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ := by
  apply mem_lconj₂;
  simpa using h;

lemma LConj₂Conj₂_of_provable {Δ : List (Formula α)} (h : ∀ δ ∈ Δ, 𝓢 ⊢ γ ➝ δ) : 𝓢 ⊢ γ ➝ Δ.conj₂ := by
  induction Δ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle φ =>
    apply h;
    simp;
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    apply ruleC;
    . apply h.1;
    . apply ih h.2;

lemma LConj₂Conj₂_of_subset {Γ Δ : List (Formula α)} (h : ∀ φ, φ ∈ Δ → φ ∈ Γ) : 𝓢 ⊢ Γ.conj₂ ➝ Δ.conj₂ := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply mem_lconj₂ $ h δ hδ;

lemma CFConjFConj_of_subset {Γ Δ : Finset (Formula α)} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := by
  apply LConj₂Conj₂_of_subset;
  simpa;

lemma FConj₂_of_LConj {Γ : List (Formula α)} : 𝓢 ⊢ Γ.conj₂ ➝ Γ.toFinset.conj := by
  apply LConj₂Conj₂_of_provable;
  intro γ hγ;
  apply mem_lconj₂;
  simpa using hγ;

lemma insert_FConj {Γ : Finset (Formula α)} : 𝓢 ⊢ φ ⋏ Γ.conj ➝ (insert φ Γ).conj := by
  apply C_replace_both $ insert_LConj;
  . show 𝓢 ⊢ φ ⋏ Γ.conj ➝ φ ⋏ ⋀Γ.toList;
    apply CKK_right_replace;
    simp;
  . show 𝓢 ⊢ ⋀(φ :: Γ.toList) ➝ (insert φ Γ).conj;
    apply C_trans FConj₂_of_LConj;
    rw [show (φ :: Γ.toList).toFinset = insert φ Γ by simp];
    exact impId;

lemma CFConjFConj_of_provable {Δ : Finset (Formula α)} (h : ∀ δ ∈ Δ, 𝓢 ⊢ γ ➝ δ) : 𝓢 ⊢ γ ➝ Δ.conj := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply C_trans impId $ h δ ?_;
  simpa using hδ;

lemma LruleC {Γ : List (Formula α)} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj₂ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle ψ => apply h; simp;
  | hcons ψ Δ he ih =>
    simp only [List.conj₂_cons_nonempty he];
    simp only [List.mem_cons, forall_eq_or_imp] at h;
    apply ruleC;
    . apply h.1;
    . apply ih h.2;

lemma FruleC {Γ : Finset (Formula α)} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj := by
  apply LruleC;
  intro γ hγ;
  apply h γ;
  simpa using hγ;

lemma CA_replace_both (h₁ : 𝓢 ⊢ φ ➝ φ') (h₂ : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋎ ψ ➝ φ' ⋎ ψ' := by
  apply ruleD;
  . apply C_trans h₁; simp;
  . apply C_trans h₂; simp;

lemma CA_replace_left (h : 𝓢 ⊢ φ' ➝ φ) : 𝓢 ⊢ φ' ⋎ ψ ➝ φ ⋎ ψ := by
  apply CA_replace_both;
  . assumption;
  . simp;

lemma CA_replace_right (h : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋎ ψ ➝ φ ⋎ ψ' := by
  apply CA_replace_both;
  . simp;
  . assumption;

lemma mem_ldisj₂ {Γ : List (Formula α)} (h : ψ ∈ Γ) : 𝓢 ⊢ ψ ➝ Γ.disj₂ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ he ih =>
    simp only [List.disj₂_cons_nonempty he];
    simp only [List.mem_cons] at h;
    rcases h with rfl | h;
    . simp;
    . apply ruleI (ih h);
      exact orIntroR;
  | _ => simp_all;

lemma mem_fdisj' {Γ : Finset ι} (Φ : ι → Formula α) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ ψ ➝ ⩖ i ∈ Γ, Φ i := by
  apply mem_ldisj₂;
  simpa;

lemma mem_fconj' {Γ : Finset ι} (Φ : ι → Formula α) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ (⩕ i ∈ Γ, Φ i) ➝ ψ := by
  apply mem_lconj₂;
  simpa;

variable [Entailment.Disjunctive 𝓢] [Entailment.Consistent 𝓢]

@[simp, grind ., deprecated]
lemma not_bot : 𝓢 ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ : ∃ φ, 𝓢 ⊬ φ := Entailment.Consistent.exists_unprovable inferInstance;
  contrapose! hφ;
  exact efq ⨀ hφ;

lemma DP_ldisj₂ {Γ : List (Formula α)} (h : 𝓢 ⊢ Γ.disj₂) : ∃ γ ∈ Γ, 𝓢 ⊢ γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp at h;
  | hsingle φ => use φ; simpa;
  | hcons ψ Δ he ih =>
    simp only [List.disj₂_cons_nonempty he] at h;
    rcases Entailment.Disjunctive.disjunctive h with (h | h);
    . use ψ;
      grind;
    . obtain ⟨γ, hγ₁, hγ₂⟩ := ih h;
      use γ;
      grind;

lemma DP_fdisj {Γ : Finset ι} (Φ : ι → Formula α) (h : 𝓢 ⊢ ⩖ i ∈ Γ, Φ i) : ∃ i ∈ Γ, 𝓢 ⊢ Φ i := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := DP_ldisj₂ h;
  simp at hφ₁;
  grind;

end Entailment.Corsi



open Entailment.Corsi

variable {L : Logic ℕ}

abbrev SubformulaOf (φ : Formula ℕ) : Type := { ψ // ψ ∈ φ.subformulas }
instance : Fintype (SubformulaOf φ) where
  elems := Finset.univ
  complete := by simp;


abbrev SubformulaSubsets (φ : Formula ℕ) := Finset (SubformulaOf φ)
abbrev HintikkaPair (φ : Formula ℕ) := (SubformulaSubsets φ) × (SubformulaSubsets φ)

namespace HintikkaPair

variable {H : HintikkaPair φ}

def Consistent (L : Logic ℕ) (H : HintikkaPair φ) : Prop := L ⊬ Finset.conj' H.1 (·.1) ➝ Finset.disj' H.2 (·.1)
lemma iff_consistent : H.Consistent L ↔ ¬(L ⊢ Finset.conj' H.1 (·.1) ➝ Finset.disj' H.2 (·.1)) := by simp [Consistent];
lemma iff_not_consistent : ¬(H.Consistent L) ↔ L ⊢ Finset.conj' H.1 (·.1) ➝ Finset.disj' H.2 (·.1) := by simp [Consistent];

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

variable [Entailment.VF L]

lemma either_consistent_insert
  (H_consis : H.Consistent L) {ψ}
  : Consistent L (H.insert₁ ψ) ∨ Consistent L (H.insert₂ ψ) := by
  contrapose! H_consis;
  apply iff_not_consistent.mpr;

  obtain ⟨h₁, h₂⟩ := H_consis;

  replace h₁ : L ⊢ Finset.conj' (H.insert₁ ψ).1 (·.1) ➝ Finset.disj' H.2 (·.1) := iff_not_consistent.mp h₁;
  replace h₂ : L ⊢ Finset.conj' H.1 (·.1) ➝ Finset.disj' (H.insert₂ ψ).2 (·.1) := iff_not_consistent.mp h₂;

  apply ruleI ?_ (ruleD h₁ impId);

  have h₃ : L ⊢ Finset.conj' H.1 (·.1) ➝ (Finset.disj' (H.insert₂ ψ).2 (·.1)) ⋏ (Finset.conj' H.2 (·.1) ⋎ Finset.conj' H.1 (·.1)) :=
    ruleC h₂ orIntroR;
  apply ruleI h₃;
  have h₄ : L ⊢ Finset.conj' H.1 (·.1) ➝ (Finset.conj' H.1 (·.1) ⋏ ψ) ⋎ (Finset.disj' H.2 (·.1)) := by
    apply ruleI h₃;
    have := collectOrAnd (𝓢 := L) (φ := Finset.disj' H.2 (·.1)) (ψ := Finset.conj' H.1 (·.1)) (χ := ψ);
    dsimp [Axioms.CollectOrAnd] at this;
    sorry;
  sorry;


namespace lindenbaum

end lindenbaum

open lindenbaum in
lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent L) : ∃ H' : HintikkaPair φ, H.1 ⊆ H'.1 ∧ H.2 ⊆ H'.2 ∧ H'.Consistent L ∧ H'.Saturated := by
  sorry;

end HintikkaPair

abbrev ConsistentSaturatedHintikkaPair (L) (φ) := { H : HintikkaPair φ // H.Consistent L ∧ H.Saturated }

namespace ConsistentSaturatedHintikkaPair

variable {H : ConsistentSaturatedHintikkaPair L φ}

open Formula

variable [Entailment.VF L]

lemma lindenbaum (H : HintikkaPair φ) (H_consis : H.Consistent L) : ∃ H' : ConsistentSaturatedHintikkaPair L φ, H.1 ⊆ H'.1.1 ∧ H.2 ⊆ H'.1.2 := by
  obtain ⟨H', _, _, H'_consis, H'_saturated⟩ := HintikkaPair.lindenbaum H H_consis;
  use ⟨H', ⟨H'_consis, H'_saturated⟩⟩;

@[simp, grind .] lemma consistent (H : ConsistentSaturatedHintikkaPair L φ) : HintikkaPair.Consistent L H.1 := H.2.1
@[simp, grind .] lemma saturated (H : ConsistentSaturatedHintikkaPair L φ) : HintikkaPair.Saturated H.1 := H.2.2

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
  . exact efq;

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

end ConsistentSaturatedHintikkaPair


namespace FMT

open Formula

variable [Entailment.VF L] [Entailment.Disjunctive L] [Entailment.Consistent L]

open Classical in
noncomputable def HintikkaModel (L : Logic ℕ) [Entailment.VF L] [Entailment.Consistent L] [Entailment.Disjunctive L] (φ : Formula ℕ) : FMT.Model :=
  letI H₀ : HintikkaPair φ := ⟨
    ∅,
    Finset.univ.filter (λ ⟨δ, hδ⟩ => ∃ χ ξ, δ = χ.1 ➝ ξ.1 ∧ ∃ H : ConsistentSaturatedHintikkaPair L φ, χ ∈ H.1.1 ∧ ξ ∈ H.1.2 )
  ⟩;
  haveI hH₀ := ConsistentSaturatedHintikkaPair.lindenbaum (φ := φ) (L := L) H₀ $ by
    apply HintikkaPair.iff_consistent.mpr;
    by_contra! hC;
    have : L ⊢ ⩖ δ ∈ H₀.2, ↑δ := hC ⨀ by simp [H₀];
    obtain ⟨δ, hδ₁, hδ₂⟩ : ∃ δ ∈ H₀.2, L ⊢ ↑δ := by
      apply DP_fdisj;
      apply Entailment.mdp! hC;
      simp [H₀];
    obtain ⟨χ, ξ, e, Γ, hΓχ, hΓξ⟩ : ∃ χ ξ : SubformulaOf φ, δ = χ.1 ➝ ξ.1 ∧ ∃ H : ConsistentSaturatedHintikkaPair L φ, χ ∈ H.1.1 ∧ ξ ∈ H.1.2  := by
      simpa [H₀] using hδ₁;
    apply Γ.consistent;
    apply C_replace_both;
    . show L ⊢ χ.1 ➝ ξ.1;
      exact e ▸ hδ₂;
    . apply mem_fconj';
      use χ;
    . apply mem_fdisj';
      use ξ;
  {
    World := ConsistentSaturatedHintikkaPair L φ
    Rel ψ H I :=
      match ψ with
      | χ ➝ ξ =>
        ∀ (h : χ ➝ ξ ∈ φ.subformulas),
          ⟨χ ➝ ξ, h⟩ ∈ H.1.2 ∨
          ⟨χ, Formula.subformulas.mem_imp h |>.1⟩ ∈ I.1.2 ∨
          ⟨ξ, Formula.subformulas.mem_imp h |>.2⟩ ∈ I.1.1
      | _ => True
    root := hH₀.choose
    rooted {ψ I} := by
      match ψ with
      | χ ➝ ξ =>
        simp only;
        rintro _;
        let χ' : SubformulaOf φ := ⟨χ, by grind⟩;
        let ξ' : SubformulaOf φ := ⟨ξ, by grind⟩;
        by_cases h : ∀ I : ConsistentSaturatedHintikkaPair L φ, χ' ∈ I.1.2 ∨ ξ' ∈ I.1.1;
        . right;
          exact h I;
        . left;
          apply hH₀.choose_spec |>.2;
          suffices ∃ χ' ξ', χ ➝ ξ = χ'.1 ➝ ξ'.1 ∧ ∃ I : ConsistentSaturatedHintikkaPair L φ, χ' ∈ I.1.1 ∧ ξ' ∈ I.1.2 by
            simpa only [H₀, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach, true_and] using this;
          push_neg at h;
          obtain ⟨I, hI₁, hI₂⟩ := h;
          use χ', ξ';
          refine ⟨?_, I, ?_, ?_⟩;
          . rfl;
          . apply ConsistentSaturatedHintikkaPair.iff_mem₁_not_mem₂.mpr hI₁;
          . apply ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mpr hI₂;
      | χ ⋏ ξ | χ ⋎ ξ | ⊥ | #a => tauto;
    Val H a := (ha : #a ∈ φ.subformulas) → ⟨#a, ha⟩ ∈ H.1.1
  }

open Formula.FMT in
lemma HintikkaModel.truthlemma {H : HintikkaModel L φ} (hsub : ψ ∈ φ.subformulas) : ⟨ψ, hsub⟩ ∈ H.1.1 ↔ H ⊩ ψ := by
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
      obtain ⟨I, hI₁, hI₂⟩ := ConsistentSaturatedHintikkaPair.lindenbaum (φ := φ) (L := L) ({⟨χ, by grind⟩}, {⟨ξ, by grind⟩}) $ by
        suffices L ⊬ χ ➝ ξ by simpa [HintikkaPair.Consistent];
        by_contra! hC;
        apply H.consistent;
        apply af;
        apply ?_ ⨀ hC;
        apply mem_fdisj';
        replace h := ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mpr h;
        use ⟨χ ➝ ξ, by tauto⟩;
      use I;
      refine ⟨?_, ?_, ?_⟩;
      . dsimp [HintikkaModel]
        grind;
      . apply ihχ (by grind) |>.mp;
        grind;
      . apply ihξ (by grind) |>.not.mp;
        apply ConsistentSaturatedHintikkaPair.iff_mem₂_not_mem₁.mp;
        grind;

end FMT


end LO.Propositional

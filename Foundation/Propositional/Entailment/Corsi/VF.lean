import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Logic.Disjunctive


namespace LO.Propositional

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

protected class VF (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasDistributeAndOr 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomVerum 𝓢,
  Entailment.HasAxiomEFQ 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢,
  Entailment.RuleC 𝓢,
  Entailment.RuleD 𝓢,
  Entailment.RuleI 𝓢

-- TODO: unify old
namespace Corsi

variable [Entailment.VF 𝓢]

instance : Entailment.HasCollectOrAnd 𝓢 where
  collectOrAnd! {φ ψ χ} := by
    apply C_trans! distributeAndOr!;
    apply CA!_of_C!_of_C!;
    . apply C_trans! andElimR! orIntroL!;
    . apply C_trans! $ C_trans! K_comm! distributeAndOr!;
      apply CA!_of_C!_of_C!;
      . apply C_trans! andElimR! orIntroL!;
      . apply C_trans! K_comm! orIntroR!


@[simp, grind ., deprecated]
lemma not_bot [Entailment.Consistent 𝓢] : 𝓢 ⊬ ⊥ := by
  obtain ⟨φ, hφ⟩ : ∃ φ, 𝓢 ⊬ φ := Entailment.Consistent.exists_unprovable inferInstance;
  contrapose! hφ;
  exact efq ⨀ hφ;


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


lemma insert_LConj {Γ : List F} : 𝓢 ⊢ φ ⋏ Γ.conj₂ ➝ (φ :: Γ).conj₂ := by
  match Γ with
  | [] => simp [List.conj₂];
  | γ :: Γ => apply ruleC andElimL andElimR;

@[simp, grind .]
lemma conjconj {Γ : Finset F} : 𝓢 ⊢ (Γ.conj) ➝ Γ.toList.conj₂ := by simp [Finset.conj];


lemma LConj₂Conj₂_of_provable {Δ : List F} (h : ∀ δ ∈ Δ, 𝓢 ⊢ γ ➝ δ) : 𝓢 ⊢ γ ➝ Δ.conj₂ := by
  induction Δ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle φ =>
    apply h;
    simp;
  | hcons ψ Δ he ih =>
    simp only [List.conj₂_cons_nonempty he];
    simp only [List.mem_cons, forall_eq_or_imp] at h;
    apply ruleC;
    . apply h.1;
    . apply ih h.2;


lemma ruleC_lconj₂ {Γ : List F} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj₂ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply af; simp;
  | hsingle ψ => apply h; simp;
  | hcons ψ Δ he ih =>
    simp only [List.conj₂_cons_nonempty he];
    simp only [List.mem_cons, forall_eq_or_imp] at h;
    apply ruleC;
    . apply h.1;
    . apply ih h.2;

lemma ruleC_fconj {Γ : Finset F} (h : ∀ γ ∈ Γ, 𝓢 ⊢ φ ➝ γ) : 𝓢 ⊢ φ ➝ Γ.conj := by
  apply ruleC_lconj₂;
  intro γ hγ;
  apply h γ;
  simpa using hγ;

lemma ruleC_fconj' {Γ : Finset ι} (Φ : ι → F) (h : ∀ i ∈ Γ, 𝓢 ⊢ φ ➝ Φ i) : 𝓢 ⊢ φ ➝ (⩕ i ∈ Γ, Φ i) := by
  apply ruleC_lconj₂;
  simpa;



lemma mem_lconj₂ {Γ : List F} (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ he ih =>
    simp [List.conj₂_cons_nonempty he];
    simp at h;
    rcases h with rfl | h;
    . simp;
    . apply C_trans ?_ $ ih h;
      simp;
  | _ => simp_all;

lemma mem_fconj {Γ : Finset F} (h : φ ∈ Γ) : 𝓢 ⊢ Γ.conj ➝ φ := by
  apply mem_lconj₂;
  simpa using h;

lemma mem_fconj' {Γ : Finset ι} (Φ : ι → F) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ (⩕ i ∈ Γ, Φ i) ➝ ψ := by
  apply mem_lconj₂;
  simpa;


lemma LConj₂Conj₂_of_subset {Γ Δ : List F} (h : ∀ φ, φ ∈ Δ → φ ∈ Γ) : 𝓢 ⊢ Γ.conj₂ ➝ Δ.conj₂ := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply mem_lconj₂ $ h δ hδ;

lemma CFConjFConj_of_subset {Γ Δ : Finset F} (h : Δ ⊆ Γ) : 𝓢 ⊢ Γ.conj ➝ Δ.conj := by
  apply LConj₂Conj₂_of_subset;
  simpa;

variable [DecidableEq F] in
lemma FConj₂_of_LConj {Γ : List F} : 𝓢 ⊢ Γ.conj₂ ➝ Γ.toFinset.conj := by
  apply LConj₂Conj₂_of_provable;
  intro γ hγ;
  apply mem_lconj₂;
  simpa using hγ;

variable [DecidableEq F] in
lemma insert_FConj {Γ : Finset F} : 𝓢 ⊢ φ ⋏ Γ.conj ➝ (insert φ Γ).conj := by
  apply C_replace_both $ insert_LConj;
  . show 𝓢 ⊢ φ ⋏ Γ.conj ➝ φ ⋏ ⋀Γ.toList;
    apply CKK_right_replace;
    simp;
  . show 𝓢 ⊢ ⋀(φ :: Γ.toList) ➝ (insert φ Γ).conj;
    apply C_trans FConj₂_of_LConj;
    rw [show (φ :: Γ.toList).toFinset = insert φ Γ by simp];
    exact impId;

lemma CFConjFConj_of_provable {Δ : Finset F} (h : ∀ δ ∈ Δ, 𝓢 ⊢ γ ➝ δ) : 𝓢 ⊢ γ ➝ Δ.conj := by
  apply LConj₂Conj₂_of_provable;
  intro δ hδ;
  apply C_trans impId $ h δ ?_;
  simpa using hδ;



lemma mem_ldisj₂ {Γ : List F} (h : ψ ∈ Γ) : 𝓢 ⊢ ψ ➝ Γ.disj₂ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ he ih =>
    simp only [List.disj₂_cons_nonempty he];
    simp only [List.mem_cons] at h;
    rcases h with rfl | h;
    . simp;
    . apply ruleI (ih h);
      exact orIntroR;
  | _ => simp_all;

lemma mem_fdisj' {Γ : Finset ι} (Φ : ι → F) (hΦ : ∃ i ∈ Γ, Φ i = ψ) : 𝓢 ⊢ ψ ➝ ⩖ i ∈ Γ, Φ i := by
  apply mem_ldisj₂;
  simpa;


lemma ruleD_ldisj₂ {Γ : List F} (h : ∀ γ ∈ Γ, 𝓢 ⊢ γ ➝ φ) : 𝓢 ⊢ Γ.disj₂ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply efq;
  | hsingle ψ => apply h; simp;
  | hcons ψ Δ he ih =>
    simp only [List.disj₂_cons_nonempty he];
    simp only [List.mem_cons, forall_eq_or_imp] at h;
    apply ruleD;
    . apply h.1;
    . apply ih h.2;

lemma ruleD_fdisj' {Γ : Finset ι} (Φ : ι → F) (h : ∀ i ∈ Γ, 𝓢 ⊢ Φ i ➝ φ) : 𝓢 ⊢ (⩖ i ∈ Γ, Φ i) ➝ φ := by
  apply ruleD_ldisj₂;
  simpa;



variable [Entailment.Disjunctive 𝓢] [Entailment.Consistent 𝓢]

lemma DP_ldisj₂ {Γ : List F} (h : 𝓢 ⊢ Γ.disj₂) : ∃ γ ∈ Γ, 𝓢 ⊢ γ := by
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

lemma DP_fdisj {Γ : Finset ι} (Φ : ι → F) (h : 𝓢 ⊢ ⩖ i ∈ Γ, Φ i) : ∃ i ∈ Γ, 𝓢 ⊢ Φ i := by
  obtain ⟨φ, hφ₁, hφ₂⟩ := DP_ldisj₂ h;
  simp at hφ₁;
  grind;

end Corsi



end Entailment


end LO.Propositional

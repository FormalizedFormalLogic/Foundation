import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

lemma _root_.List.empty_def {Γ : List α} : Γ = [] ↔ ∀ p, p ∉ Γ := by induction Γ <;> simp_all;

namespace LO.Propositional.Superintuitionistic

open System FiniteContext
open Formula Formula.Kripke

variable [DecidableEq α]
variable {Λ : AxiomSet α} [HasEFQ Λ]

def Tableau (α) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ t.1) → (∀ p ∈ Δ, p ∈ t.2) → Λ ⊬! Γ.conj' ⟶ Δ.disj'

variable (hCon : Consistent Λ t)

def consistent_either (p : Formula α) : Consistent Λ (insert p t.1, t.2) ∨ Consistent Λ (t.1, insert p t.2) := by
  by_contra hC;
  obtain ⟨⟨Γ₁, hΓ₁, Δ₁, hΔ₁, hC₁⟩, ⟨Γ₂, hΓ₂, Δ₂, hΔ₂, hC₂⟩⟩ := by simpa only [Consistent, not_or, not_forall, not_not, exists_prop, exists_and_left] using hC;
  simp_all;
  sorry;
  -- replace hC₁ : Λ ⊢! ⋀(Γ₁.remove p) ⋏ p ⟶ ⋁Δ₁ := implyLeftRemoveConj hC₁;
  -- replace hC₂ : Λ ⊢! ⋀Γ₂ ⟶ ⋁(Δ₂.remove p) ⋎ p := implyRightRemoveDisj hC₂;
  -- have : Λ ⊢! ⋀(Γ₁.remove p) ⋏ p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂) := imp_trans! hC₁ (by simp)
  -- have : Λ ⊢! ⋀(Γ₁.remove p) ⟶ (p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂)) := andImplyIffImplyImply'!.mp this;
  -- sorry;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₂, hp₁, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [Consistent] at hCon;
  have : Λ ⊬! [p].conj' ⟶ [p].disj' := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : Λ ⊢! [p].conj' ⟶ [p].disj' := by simp;
  contradiction;

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.1) (h : Λ ⊢! Γ.conj' ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! Γ.conj' ⟶ [q].disj' := by simpa;
  have : Λ ⊬! Γ.conj' ⟶ [q].disj' := hCon (by aesop) (by aesop);
  contradiction;

def Saturated (t : Tableau α) := ∀ p : Formula α, p ∈ t.1 ∨ p ∈ t.2

variable (hMat : Saturated t := by simpa)

lemma mem₂_of_not_mem₁ : p ∉ t.1 → p ∈ t.2 := by
  intro h;
  cases (hMat p) with
  | inl h' => exact absurd h' h;
  | inr _ => assumption;

lemma mem₁_of_not_mem₂ : p ∉ t.2 → p ∈ t.1 := by
  intro h;
  cases (hMat p) with
  | inl _ => assumption;
  | inr h' => exact absurd h' h;

lemma not_mem₁_iff_mem₂ : p ∉ t.1 ↔ p ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma not_mem₂_iff_mem₁ : p ∉ t.2 ↔ p ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hMat;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon;

section lindenbaum

lemma lindenbaum (hCon : Consistent Λ t₀) : ∃ t, t₀ ⊆ t ∧ (Consistent Λ t) ∧ (Saturated t) := by sorry;

end lindenbaum

end Tableau

structure SaturatedConsistentTableau (Λ : AxiomSet α) where
  tableau : Tableau α
  saturated : tableau.Saturated
  consistent : tableau.Consistent Λ

namespace SaturatedConsistentTableau

lemma lindenbaum (hCon : t₀.Consistent Λ) : ∃ (t : SaturatedConsistentTableau Λ), t₀ ⊆ t.tableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

variable (t : SaturatedConsistentTableau Λ)

@[simp] lemma disjoint : Disjoint t.tableau.1 t.tableau.2 := t.tableau.disjoint_of_consistent t.consistent

lemma not_mem₁_iff_mem₂ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma not_mem₂_iff_mem₁ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

variable {t : SaturatedConsistentTableau Λ}

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.tableau.1) (h : Λ ⊢! Γ.conj' ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp (hp : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  exact t.not_mem₂_iff_mem₁.mp $ not_mem₂ (by simpa) (show Λ ⊢! List.conj' [p] ⟶ q by simpa;)

@[simp]
lemma mem_verum : ⊤ ∈ t.tableau.1 := by
  apply t.not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : Λ ⊬! [].conj' ⟶ [⊤].disj' := t.consistent (by simp) (by simpa);
  have : Λ ⊢! [].conj' ⟶ [⊤].disj' := by simp;
  contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! [⊥].conj' ⟶ [].disj' := t.consistent (by simpa) (by simp);
  have : Λ ⊢! [⊥].conj' ⟶ [].disj' := by simp;
  contradiction;

@[simp]
lemma iff_mem_conj : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp h (by simp)
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    have : Λ ⊢! [p, q].conj' ⟶ [p ⋏ q].disj' := by simp;
    have : Λ ⊬! [p, q].conj' ⟶ [p ⋏ q].disj' := t.consistent (by aesop) (by simpa using t.not_mem₁_iff_mem₂.mp hC);
    contradiction;

@[simp]
lemma iff_mem_disj : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.1;
    have : q ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.2;
    have : Λ ⊢! [p ⋎ q].conj' ⟶ [p, q].disj' := by simp;
    have : Λ ⊬! [p ⋎ q].conj' ⟶ [p, q].disj' := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp h disj₁!
    | inr h => exact mdp h disj₂!

end SaturatedConsistentTableau


namespace Kripke

def CanonicalModel (Λ : AxiomSet α) : Model (𝐈𝐧𝐭 (SaturatedConsistentTableau Λ) α) where
  frame := λ t₁ t₂ => t₁.tableau.1 ⊆ t₂.tableau.1
  valuation := λ t a => (atom a) ∈ t.tableau.1
  hereditary := by aesop;
  frame_prop := by simp [FrameClass.Intuitionistic, Transitive, Reflexive]; tauto;

namespace CanonicalModel

@[simp] lemma frame_def {t₁ t₂ : SaturatedConsistentTableau Λ} : (CanonicalModel Λ).frame t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {t : SaturatedConsistentTableau Λ} {a : α} : (CanonicalModel Λ).valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end CanonicalModel

variable {t : SaturatedConsistentTableau Λ}

lemma truthlemma : ((CanonicalModel Λ), t) ⊧ p ↔ p ∈ t.tableau.1 := by
  induction p using rec' generalizing t with
  | himp p q ihp ihq =>
    constructor;
    . contrapose;
      intro h;
      simp [Satisfies.imp_def];
      replace h := t.not_mem₁_iff_mem₂.mp h;
      have : Tableau.Consistent Λ (insert p t.tableau.1, {q}) := by
        simp only [Tableau.Consistent];
        intro Γ Δ hΓ hΔ;
        replace hΓ : ∀ r, r ∈ Γ.remove p → r ∈ t.tableau.1 := by
          intro r hr;
          have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
          have := by simpa using hΓ r hr₁;
          simp_all;
        by_contra hC;
        have : Λ ⊢! (Γ.remove p).conj' ⟶ (p ⟶ q) := imp_trans! (andImplyIffImplyImply'!.mp $ implyLeftRemoveConj hC) (by
          apply provable_iff_provable.mpr;
          apply deduct_iff.mpr;
          apply deduct_iff.mpr;
          have : [p, p ⟶ Δ.disj'] ⊢[Λ]! p := by_axm! (by simp);
          have : [p, p ⟶ Δ.disj'] ⊢[Λ]! Δ.disj' := (by_axm! (by simp)) ⨀ this;
          exact disj_allsame'! (by simpa using hΔ) this;
        )
        have : Λ ⊬! (Γ.remove p).conj' ⟶ (p ⟶ q) := by simpa only [List.disj'_singleton] using (t.consistent hΓ (show ∀ r ∈ [p ⟶ q], r ∈ t.tableau.2 by simp_all));
        contradiction;
      obtain ⟨t', ⟨⟨_, _⟩, _⟩⟩ := by simpa [Set.insert_subset_iff] using SaturatedConsistentTableau.lindenbaum this;
      existsi t';
      simp_all;
      apply t'.not_mem₁_iff_mem₂.mpr;
      simpa
    . simp [Satisfies.imp_def];
      intro h t' htt' hp;
      replace hp := ihp.mp hp;
      have hpq := htt' h;
      apply ihq.mpr;
      apply t'.not_mem₂_iff_mem₁.mp;
      exact SaturatedConsistentTableau.not_mem₂
        (by simp_all)
        (show Λ ⊢! [p, p ⟶ q].conj' ⟶ q by
          simp;
          apply provable_iff_provable.mpr;
          apply deduct_iff.mpr;
          have : [p ⋏ (p ⟶ q)] ⊢[Λ]! p ⋏ (p ⟶ q) := by_axm! (by simp);
          exact (conj₂'! this) ⨀ (conj₁'! this);
        );
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma deducible_of_validOnCanonicelModel : (CanonicalModel Λ) ⊧ p → Λ ⊢! p := by
  contrapose;
  intro h;
  have : Tableau.Consistent Λ (∅, {p}) := by
    simp only [Tableau.Consistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    replace hΓ : Γ = [] := List.empty_def.mpr hΓ;
    subst hΓ;
    have : Λ ⊢! p := disj_allsame'! hΔ (hC ⨀ verum!);
    contradiction;
  obtain ⟨t', ht'⟩ := SaturatedConsistentTableau.lindenbaum this;
  simp [ValidOnModel.iff_models, ValidOnModel]
  existsi t';
  apply truthlemma.not.mpr;
  apply t'.not_mem₁_iff_mem₂.mpr;
  simp_all;

lemma complete! : (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) ⊧ p → 𝐄𝐅𝐐 ⊢! p := by
  contrapose;
  intro h₁ h₂;
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass] at h₂;
  have : 𝐄𝐅𝐐 ⊢! p := deducible_of_validOnCanonicelModel $ @h₂ (CanonicalModel 𝐄𝐅𝐐);
  contradiction;

instance : Complete (𝐄𝐅𝐐 : AxiomSet α) (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) := ⟨complete!⟩

end Kripke

end LO.Propositional.Superintuitionistic

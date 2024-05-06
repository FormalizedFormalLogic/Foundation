import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

def singleton_conj_disj : 𝓢 ⊢ ({p} : Finset F).conj ⟶ ({p} : Finset F).disj := by
  simp [Finset.conj, Finset.disj];
  apply emptyPrf;
  apply deduct;
  have : [p ⋏ ⊤] ⊢[𝓢] p ⋏ ⊤ := FiniteContext.byAxm (by simp);
  exact disj₁' $ conj₁' this;

lemma singleton_conj_disj! : 𝓢 ⊢! ({p} : Finset F).conj ⟶ ({p} : Finset F).disj := ⟨singleton_conj_disj⟩

lemma elimAndTrue' (h : 𝓢 ⊢ p ⋏ ⊤) : 𝓢 ⊢ p := conj₁' h
lemma elimAndTrue'! (h : 𝓢 ⊢! p ⋏ ⊤) : 𝓢 ⊢! p := ⟨elimAndTrue' h.some⟩

lemma introAndTrue' (h : 𝓢 ⊢ p) : 𝓢 ⊢ p ⋏ ⊤ := conj₃' h verum
lemma introAndTrue'! (h : 𝓢 ⊢! p) : 𝓢 ⊢! p ⋏ ⊤ := ⟨introAndTrue' h.some⟩

lemma iffAndTrue'! : 𝓢 ⊢! p ⋏ ⊤ ↔ 𝓢 ⊢! p := by
  constructor;
  . intro h; apply elimAndTrue'! h;
  . intro h; apply introAndTrue'! h;

lemma elimAndTrue : 𝓢 ⊢ p ⋏ ⊤ ⟶ p := by
  apply emptyPrf;
  apply deduct;
  apply elimAndTrue';
  simpa using FiniteContext.byAxm (by simp);
@[simp] lemma elimAndTrue! : 𝓢 ⊢! p ⋏ ⊤ ⟶ p := ⟨elimAndTrue⟩

lemma introAndTrue : 𝓢 ⊢ p ⟶ p ⋏ ⊤ := by
  apply emptyPrf;
  apply deduct;
  apply introAndTrue';
  simpa using FiniteContext.byAxm (by simp);
@[simp] lemma introAndTrue! : 𝓢 ⊢! p ⟶ p ⋏ ⊤ := ⟨introAndTrue⟩

lemma implyLeftFinsetSingletonConj.mp (h : 𝓢 ⊢ (Finset.conj {p}) ⟶ q) : (𝓢 ⊢ p ⟶ q) := by
  simp [Finset.conj] at h;
  apply impTrans introAndTrue h;

lemma implyLeftFinsetSingletonConj.mpr (h : 𝓢 ⊢ p ⟶ q) : (𝓢 ⊢ (Finset.conj {p}) ⟶ q):= by
  simp [Finset.conj];
  apply impTrans elimAndTrue h;

lemma implyLeftFinsetSingletonConj! : (𝓢 ⊢! (Finset.conj {p}) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetSingletonConj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetSingletonConj.mpr h⟩;

end LO.System

namespace LO.Propositional.Superintuitionistic

open System
open Formula Formula.Kripke

variable [DecidableEq α]
variable {Λ : AxiomSet α}

abbrev FiniteTheory (α) := Finset (Formula α)

def Tableau (α) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ Γ Δ : FiniteTheory α, (↑Γ ⊆ t.1 ∧ ↑Δ ⊆ t.2) → Λ ⊬! Γ.conj ⟶ Δ.disj

variable (hCon : Consistent Λ t := by simpa)

def which (p : Formula α) : Consistent Λ (insert p t.1, t.2) ∨ Consistent Λ (t.1, insert p t.2) := by
  by_contra hC;
  obtain ⟨⟨Γ₁, Δ₁, hΔ₁, hΓ₁, hC₁⟩, ⟨Γ₂, Δ₂, hΔ₂, hΓ₂, hC₂⟩⟩ := by simpa [not_or, Consistent] using hC;
  sorry;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₂, hp₁, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [Consistent] at hCon;
  have : Λ ⊬! Finset.conj {p} ⟶ Finset.disj {p} := hCon {p} {p} (by aesop) (by aesop);
  have : Λ ⊢! Finset.conj {p} ⟶ Finset.disj {p} := System.singleton_conj_disj!;
  contradiction;

lemma singleton₂ {Γ : FiniteTheory α} (hΓ : ↑Γ ⊆ t.1) (h : Λ ⊢ Γ.conj ⟶ q) : q ∉ t.2 := by sorry;

def Saturated (t : Tableau α) := ∀ p : Formula α, p ∈ t.1 ∨ p ∈ t.2

variable (hMat : Saturated t := by simpa)

lemma each₁ : p ∉ t.1 → p ∈ t.2 := by
  intro h;
  cases (hMat p) with
  | inl h' => exact absurd h' h;
  | inr _ => assumption;

lemma each₂ : p ∉ t.2 → p ∈ t.1 := by
  intro h;
  cases (hMat p) with
  | inl _ => assumption;
  | inr h' => exact absurd h' h;

lemma each₁' : p ∉ t.1 ↔ p ∈ t.2 := by
  constructor;
  . apply each₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma each₂' : p ∉ t.2 ↔ p ∈ t.1 := by
  constructor;
  . apply each₂ hMat;
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

lemma each₁ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.each₁' t.consistent t.saturated

lemma each₂ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.each₂' t.consistent t.saturated

variable {t : SaturatedConsistentTableau Λ}

lemma singleton₂ {Γ : FiniteTheory α} (hΓ : ↑Γ ⊆ t.tableau.1) (h : Λ ⊢ Γ.conj ⟶ q) : q ∉ t.tableau.2 := t.tableau.singleton₂ hΓ h


lemma mdp (hp : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  have : q ∉ t.tableau.2 := by sorry;
  exact t.each₂.mp (by assumption)

@[simp]
lemma verum : ⊤ ∈ t.tableau.1 := by
  apply Tableau.each₂' t.consistent t.saturated |>.mp;
  by_contra hC;
  have : Λ ⊬! Finset.conj ∅ ⟶ Finset.disj {⊤} := by simpa [Tableau.Consistent] using t.consistent _ _ (by simpa);
  have : Λ ⊢! Finset.conj ∅ ⟶ Finset.disj {⊤} := by simp [Finset.conj, Finset.disj];
  contradiction;

@[simp]
lemma falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! Finset.conj {⊥} ⟶ Finset.disj ∅ := by simpa [Tableau.Consistent] using t.consistent _ _ (by simpa);
  have : Λ ⊢! Finset.conj {⊥} ⟶ Finset.disj ∅ := by simp [Finset.conj, Finset.disj];
  contradiction;

@[simp]
lemma conj : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp h (by simp)
  . intro h;
    have : Λ ⊢! Finset.conj {p, q} ⟶ p ⋏ q := by sorry;
    have : p ⋏ q ∉ t.tableau.2 := absurd this (by
      sorry
    )
      -- have : Λ ⊬! Finset.conj {p, q} ⟶ p ⋏ q := by sorry -- simpa [Tableau.Consistent] using t.consistent _ _ (by simpa);
      -- exact absurd d this;
    exact t.each₂.mp this;

@[simp]
lemma disj : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.each₁.mp hC.1;
    have : q ∈ t.tableau.2 := t.each₁.mp hC.2;
    have : ↑({p, q} : FiniteTheory α) ⊆ t.tableau.2 := by sorry;

    have : Λ ⊢! Finset.conj {(p ⋎ q)} ⟶ Finset.disj {p, q} := by sorry;
    have := t.consistent {p ⋎ q} {p, q} (by constructor <;> simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp h (by simp)
    | inr h => exact mdp h (by simp)

/- TODO: Maybe this cannot be proved
lemma closed (t : MCT Λ) : Λ ⊢! p ↔ p ∈ t.tableau.1 := by
  induction p using Formula.rec' with
  | hand p q ihp ihq =>
    simp_all;
    constructor;
    . intro h;
      have := conj₁'! h;
      have := conj₂'! h;
      simp_all;
    . rintro ⟨hp, hq⟩;
      simp_all;
      exact conj₃'! (by assumption) (by assumption);
  | hor p q ihp ihq =>
    simp_all;
    constructor;
    . intro h;
      sorry;
    . rintro (hp | hq);
      exact disj₁'! (ihp.mpr hp);
      exact disj₂'! (ihq.mpr hq);
  | hverum => simp_all;
  | hatom =>
    constructor;
    . intro h;
      apply t.each₂.mp;
-/

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
      have := t.each₁.mp h;
      sorry;
    . simp [Satisfies.imp_def];
      intro h t' htt' hp;

      replace hp := ihp.mp hp;
      have hpq := htt' h;

      apply ihq.mpr;
      apply t'.each₂.mp;
      exact SaturatedConsistentTableau.singleton₂
        (show ↑({p, p ⟶ q} : FiniteTheory α) ⊆ t'.tableau.1 by
          sorry;
        )
        (by
          sorry
        );
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma deducible_of_validOnCanonicelModel : (CanonicalModel Λ) ⊧ p → Λ ⊢! p := by
  contrapose;
  intro h;
  have : Tableau.Consistent Λ (∅, {p}) := by sorry;
  obtain ⟨t', ht'⟩ := SaturatedConsistentTableau.lindenbaum this;
  simp [ValidOnModel.iff_models, ValidOnModel]
  existsi t';
  apply truthlemma.not.mpr;
  apply t'.each₁.mpr;
  simp_all;

lemma complete! : (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) ⊧ p → 𝐄𝐅𝐐 ⊢! p := by
  contrapose;
  intro h₁ h₂;
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass] at h₂;
  have := deducible_of_validOnCanonicelModel $ @h₂ (CanonicalModel (𝐄𝐅𝐐 : AxiomSet α));
  contradiction;

instance : Complete (𝐄𝐅𝐐 : AxiomSet α) (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) := ⟨complete!⟩

end Kripke

end LO.Propositional.Superintuitionistic

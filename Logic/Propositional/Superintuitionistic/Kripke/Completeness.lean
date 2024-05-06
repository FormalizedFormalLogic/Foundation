import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

@[simp]
lemma _root_.Set.subset_doubleton {s : Set α} {a b : α} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . aesop;
  . rintro ⟨ha, hb⟩;
    apply Set.insert_subset; exact ha;
    simp_all;

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

def singleton_conj_disj : 𝓢 ⊢ ⋀{p} ⟶ ⋁{p} := by
  simp [Finset.conj, Finset.disj];
  apply emptyPrf;
  apply deduct;
  have : [p ⋏ ⊤] ⊢[𝓢] p ⋏ ⊤ := FiniteContext.byAxm (by simp);
  exact disj₁' $ conj₁' this;

lemma singleton_conj_disj! : 𝓢 ⊢! ⋀{p} ⟶ ⋁{p} := ⟨singleton_conj_disj⟩

def signletonConjDisj : 𝓢 ⊢ [p].conj ⟶ [p].disj := by
  simp [Finset.conj, Finset.disj];
  apply emptyPrf;
  apply deduct;
  have : [p ⋏ ⊤] ⊢[𝓢] p ⋏ ⊤ := FiniteContext.byAxm (by simp);
  exact disj₁' $ conj₁' this;

@[simp] lemma signletonConjDisj! : 𝓢 ⊢! [p].conj ⟶ [p].disj := ⟨signletonConjDisj⟩

lemma elimAndTrue' (h : 𝓢 ⊢ p ⋏ ⊤) : 𝓢 ⊢ p := conj₁' h
@[simp] lemma elimAndTrue'! (h : 𝓢 ⊢! p ⋏ ⊤) : 𝓢 ⊢! p := ⟨elimAndTrue' h.some⟩

lemma introAndTrue' (h : 𝓢 ⊢ p) : 𝓢 ⊢ p ⋏ ⊤ := conj₃' h verum
@[simp] lemma introAndTrue'! (h : 𝓢 ⊢! p) : 𝓢 ⊢! p ⋏ ⊤ := ⟨introAndTrue' h.some⟩

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


lemma elimOrFalse' [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⋎ ⊥) : 𝓢 ⊢ p := disj₃' (impId _) efq h
@[simp] lemma elimOrFalse'! [HasEFQ 𝓢] (h : 𝓢 ⊢! p ⋎ ⊥) : 𝓢 ⊢! p := ⟨elimOrFalse' h.some⟩

lemma introOrFalse' (h : 𝓢 ⊢ p) : 𝓢 ⊢ p ⋎ ⊥ := disj₁' h
@[simp] lemma introOrFalse'! (h : 𝓢 ⊢! p) : 𝓢 ⊢! p ⋎ ⊥ := ⟨introOrFalse' h.some⟩

lemma iffOrFalse'! [HasEFQ 𝓢] : 𝓢 ⊢! p ⋎ ⊥ ↔ 𝓢 ⊢! p := by
  constructor;
  . intro h; apply elimOrFalse'! h;
  . intro h; apply introOrFalse'! h;

lemma elimOrFalse [HasEFQ 𝓢] : 𝓢 ⊢ p ⋎ ⊥ ⟶ p := by
  apply emptyPrf;
  apply deduct;
  apply elimOrFalse';
  simpa using FiniteContext.byAxm (by simp);
@[simp] lemma elimOrFalse! [HasEFQ 𝓢] : 𝓢 ⊢! p ⋎ ⊥ ⟶ p := ⟨elimOrFalse⟩

lemma introOrFalse : 𝓢 ⊢ p ⟶ p ⋎ ⊥ := by
  apply emptyPrf;
  apply deduct;
  apply introOrFalse';
  simpa using FiniteContext.byAxm (by simp);
@[simp] lemma introOrFalse! : 𝓢 ⊢! p ⟶ p ⋎ ⊥ := ⟨introOrFalse⟩

lemma implyLeftFinsetSingletonConj.mp (h : 𝓢 ⊢ (⋀{p}) ⟶ q) : (𝓢 ⊢ p ⟶ q) := by
  simp [Finset.conj] at h;
  exact impTrans introAndTrue h;

lemma implyLeftFinsetSingletonConj.mpr (h : 𝓢 ⊢ p ⟶ q) : (𝓢 ⊢ (⋀{p}) ⟶ q):= by
  simp [Finset.conj];
  exact impTrans elimAndTrue h;

lemma implyLeftFinsetSingletonConj! : (𝓢 ⊢! (⋀{p}) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetSingletonConj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetSingletonConj.mpr h⟩;


lemma implyRightFinsetSingletonDisj.mp [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ (⋁{q})) : (𝓢 ⊢ p ⟶ q) := by
  simp [Finset.disj] at h;
  exact impTrans h elimOrFalse;

lemma implyRightFinsetSingletonDisj.mpr [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ q) : (𝓢 ⊢ p ⟶ (⋁{q})) := by
  simp [Finset.disj];
  exact impTrans h introOrFalse;

lemma implyRightFinsetSingletonDisj! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ (⋁{q})) ↔ (𝓢 ⊢! p ⟶ q) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetSingletonDisj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetSingletonDisj.mpr h⟩;

lemma elimAndAndTrue' (h : 𝓢 ⊢ p ⋏ q ⋏ ⊤) : 𝓢 ⊢ p ⋏ q := by sorry;
lemma elimAndAndTrue : 𝓢 ⊢ p ⋏ q ⋏ ⊤ ⟶ p ⋏ q := by
  apply emptyPrf;
  apply deduct;
  apply elimAndAndTrue';
  simpa using FiniteContext.byAxm (by simp);

lemma introAndAndTrue' (h : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ p ⋏ q ⋏ ⊤ := by sorry;
lemma introAndAndTrue : 𝓢 ⊢ p ⋏ q ⟶ p ⋏ q ⋏ ⊤ := by
  apply emptyPrf;
  apply deduct;
  apply introAndAndTrue';
  simpa using FiniteContext.byAxm (by simp);

lemma implyLeftListDoubletonConj.mp (h : 𝓢 ⊢ (List.conj [p, q]) ⟶ r) : (𝓢 ⊢ p ⋏ q ⟶ r) := by
  simp [Finset.conj] at h;
  exact impTrans introAndAndTrue h;

lemma implyLeftListDoubletonConj.mpr (h : 𝓢 ⊢ p ⋏ q ⟶ r) : (𝓢 ⊢ (List.conj [p, q]) ⟶ r) := by
  simp [Finset.conj];
  exact impTrans elimAndAndTrue h;

lemma implyLeftListDoubletonConj! : (𝓢 ⊢! (List.conj [p, q]) ⟶ r) ↔ (𝓢 ⊢! p ⋏ q ⟶ r) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyLeftListDoubletonConj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyLeftListDoubletonConj.mpr h⟩;

lemma implyLeftFinsetDoubletonConj.mp (h : 𝓢 ⊢ (⋀{p, q}) ⟶ r) : (𝓢 ⊢ p ⋏ q ⟶ r) := by sorry;

lemma implyLeftFinsetDoubletonConj.mpr (h : 𝓢 ⊢ p ⋏ q ⟶ r) : (𝓢 ⊢ (⋀{p, q}) ⟶ r) := by sorry;

lemma implyLeftFinsetDoubletonConj! : (𝓢 ⊢! (⋀{p, q}) ⟶ r) ↔ (𝓢 ⊢! p ⋏ q ⟶ r) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetDoubletonConj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyLeftFinsetDoubletonConj.mpr h⟩;

lemma implyRightFinsetDoubletonDisj.mp [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ (⋁{q, r})) : (𝓢 ⊢ p ⟶ q ⋎ r) := by sorry;

lemma implyRightFinsetDoubletonDisj.mpr [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ q ⋎ r) : (𝓢 ⊢ p ⟶ (⋁{q, r})) := by sorry;

lemma implyRightFinsetDoubletonDisj! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ (⋁{q, r})) ↔ (𝓢 ⊢! p ⟶ q ⋎ r) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetDoubletonDisj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetDoubletonDisj.mpr h⟩;

lemma implyLeftListInsertConj.mp (h : 𝓢 ⊢ (List.conj (p :: Γ)) ⟶ q) : (𝓢 ⊢ p ⋏ Γ.conj ⟶ q) := by simpa [List.conj];

lemma implyLeftListInsertConj.mpr (h : 𝓢 ⊢ p ⋏ Γ.conj ⟶ q) : (𝓢 ⊢ (List.conj (p :: Γ)) ⟶ q) := by simpa [List.conj];

lemma implyLeftListInsertConj! : (𝓢 ⊢! (List.conj (p :: Γ)) ⟶ q) ↔ (𝓢 ⊢! p ⋏ Γ.conj ⟶ q) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyLeftListInsertConj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyLeftListInsertConj.mpr h⟩;

variable {T : Set F} {Γ Δ : Finset F}

lemma list_conj_iff! {Γ : List F} : (𝓢 ⊢! Γ.conj) ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ
  case nil => simp;
  case cons p Δ ih =>
    simp;
    constructor
    · intro h; exact ⟨conj₁'! h, ih.mp (conj₂'! h)⟩
    · intro h; exact conj₃'! h.1 (ih.mpr h.2)

lemma finset_conj_iff! : (𝓢 ⊢! ⋀Γ) ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by simp [Finset.conj, list_conj_iff!]

lemma iffConjInsertFinset'! : 𝓢 ⊢! ⋀(insert p Γ) ↔ 𝓢 ⊢! p ⋏ ⋀Γ := by
  constructor;
  . intro h;
    have h₁ := finset_conj_iff!.mp h;
    exact conj₃'! (h₁ p (by simp)) (by apply finset_conj_iff!.mpr; intro p hp; exact h₁ p (by simp [hp]));
  . intro h;
    have := conj₁'! h;
    have := finset_conj_iff!.mp $ conj₂'! h;
    apply finset_conj_iff!.mpr;
    intro q hq;
    cases Finset.mem_insert.mp hq <;> simp_all

lemma iffConjInsertFinset! : 𝓢 ⊢! ⋀(insert p Γ) ⟷ p ⋏ ⋀Γ := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjInsertFinset'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjInsertFinset'!.mpr;
    exact by_axm! (by simp);

lemma implyLeftReplace! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  simp [LogicalConnective.iff] at h;
  constructor;
  . intro hpr; exact imp_trans! (conj₂'! h) hpr;
  . intro hqr; exact imp_trans! (conj₁'! h) hqr;

lemma implyRightReplace! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  simp [LogicalConnective.iff] at h;
  constructor;
  . intro hrp; exact imp_trans! hrp (conj₁'! h);
  . intro hrq; exact imp_trans! hrq (conj₂'! h);

lemma implaa! : (𝓢 ⊢! ⋀(insert p Γ) ⟶ q) ↔ (𝓢 ⊢! p ⋏ ⋀Γ ⟶ q) := by
  apply implyLeftReplace!;
  apply iffConjInsertFinset!;

lemma andImplyIffImplyImply! (p q r) : 𝓢 ⊢! (p ⋏ q ⟶ r) ⟷ (p ⟶ q ⟶ r) := ⟨andImplyIffImplyImply p q r⟩

lemma andImplyIffImplyImply'! : (𝓢 ⊢! p ⋏ q ⟶ r) ↔ (𝓢 ⊢! p ⟶ q ⟶ r) := by
  have H : 𝓢 ⊢! (p ⋏ q ⟶ r) ⟷ (p ⟶ q ⟶ r) := andImplyIffImplyImply! p q r;
  constructor;
  . intro h; exact (conj₁'! H) ⨀ h;
  . intro h; exact (conj₂'! H) ⨀ h;


end LO.System

namespace LO.Propositional.Superintuitionistic

variable [DecidableEq α]

-- instance : Coe (List (Formula α)) (Theory α) := ⟨λ Γ => ↑Γ.toFinset⟩

open System FiniteContext
open Formula Formula.Kripke

variable {Λ : AxiomSet α} [HasEFQ Λ]

def Tableau (α) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ {Γ Δ : Finset (Formula α)}, ↑Γ ⊆ t.1 → ↑Δ ⊆ t.2 → Λ ⊬! ⋀Γ ⟶ ⋁Δ

variable (hCon : Consistent Λ t)

def which (p : Formula α) : Consistent Λ (insert p t.1, t.2) ∨ Consistent Λ (t.1, insert p t.2) := by
  by_contra hC;
  obtain ⟨⟨Γ₁, hΓ₁, Δ₁, hΔ₁, hC₁⟩, ⟨Γ₂, hΓ₂, Δ₂, hΔ₂, hC₂⟩⟩ := by simpa only [Consistent, not_or, not_forall, not_not, exists_prop, exists_and_left] using hC;
  sorry;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₂, hp₁, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [Consistent] at hCon;
  have : Λ ⊬! ⋀{p} ⟶ ⋁{p} := hCon (by aesop) (by aesop);
  have : Λ ⊢! ⋀{p} ⟶ ⋁{p} := by
    simp [Finset.conj, Finset.disj];
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    have : [p ⋏ ⊤] ⊢[Λ]! p ⋏ ⊤ := by_axm! (by simp);
    exact disj₁'! $ conj₁'! this;
  contradiction;

lemma not_mem₂ {Γ : Finset (Formula α)} (hΓ : ↑Γ ⊆ t.1) (h : Λ ⊢! ⋀Γ ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! ⋀Γ ⟶ ⋁{q} := implyRightFinsetSingletonDisj!.mpr h;
  have : Λ ⊬! ⋀Γ ⟶ ⋁{q} := hCon (by aesop) (by aesop);
  contradiction;

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

lemma mem_either₁ : p ∉ t.1 ↔ p ∈ t.2 := by
  constructor;
  . apply each₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma mem_either₂ : p ∉ t.2 ↔ p ∈ t.1 := by
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

lemma mem_either₁ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.mem_either₁ t.consistent t.saturated

lemma mem_either₂ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.mem_either₂ t.consistent t.saturated

variable {t : SaturatedConsistentTableau Λ}

lemma not_mem₂ {Γ : Finset (Formula α)} (hΓ : ↑Γ ⊆ t.tableau.1) (h : Λ ⊢! ⋀Γ ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp (hp : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  exact t.mem_either₂.mp $ not_mem₂
    (show ↑({p} : Finset _) ⊆ t.tableau.1 by simpa)
    (by apply implyLeftFinsetSingletonConj!.mpr; simpa)

@[simp]
lemma verum : ⊤ ∈ t.tableau.1 := by
  apply t.mem_either₂.mp;
  by_contra hC;
  have : Λ ⊬! (⋀∅) ⟶ (⋁{⊤}) := by simpa [Tableau.Consistent] using t.consistent (by simp) (by simpa);
  have : Λ ⊢! (⋀∅) ⟶ (⋁{⊤}) := by simp [Finset.conj, Finset.disj];
  contradiction;

@[simp]
lemma falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! ⋀{⊥} ⟶ ⋁∅ := by simpa [Tableau.Consistent] using t.consistent (by simpa) (by simp);
  have : Λ ⊢! ⋀{⊥} ⟶ ⋁∅ := by simp [Finset.conj, Finset.disj];
  contradiction;

@[simp]
lemma conj : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp h (by simp)
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    have : Λ ⊢! (⋀{p, q}) ⟶ (⋁{p ⋏ q}) := by
      apply implyRightFinsetSingletonDisj!.mpr;
      apply implyLeftFinsetDoubletonConj!.mpr;
      simp;
    have : Λ ⊬! (⋀{p, q}) ⟶ (⋁{p ⋏ q}) := t.consistent
      (by simp_all)
      (by simpa using t.mem_either₁.mp hC);
    contradiction;

@[simp]
lemma disj : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.mem_either₁.mp hC.1;
    have : q ∈ t.tableau.2 := t.mem_either₁.mp hC.2;
    have : Λ ⊢! ⋀{(p ⋎ q)} ⟶  ⋁{p, q} := by
      apply implyLeftFinsetSingletonConj!.mpr;
      apply implyRightFinsetDoubletonDisj!.mpr;
      simp;
    have : Λ ⊬! ⋀{(p ⋎ q)} ⟶  ⋁{p, q} := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp h (by simp)
    | inr h => exact mdp h (by simp)

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
      replace h := t.mem_either₁.mp h;
      have : Tableau.Consistent Λ (insert p t.tableau.1, {q}) := by
        simp only [Tableau.Consistent];
        intro Γ Δ hΓ hΔ;
        replace hΔ : Δ = ∅ ∨ Δ = {q} := by simpa using Set.subset_singleton_iff_eq.mp hΔ;
        cases hΔ with
        | inl h =>
          subst h;
          simp [Finset.disj];
          by_contra hC;
          sorry;
          -- have : Λ ⊢! (⋀(Γ.erase p) ⋏ p) ⟶ ⊥ := by sorry; -- insertexpand hΓ hC;
          -- have : Λ ⊢! (⋀(Γ.erase p) ⋏ p) ⟶ ⋁∅ := by simpa [Finset.disj];
          -- have : Λ ⊬! (⋀(Γ.erase p) ⋏ p) ⟶ ⋁∅ := t.consistent (by sorry) (by sorry);
          -- contradiction;
        | inr h =>
          subst h;
          apply implyRightFinsetSingletonDisj!.not.mpr;
          by_contra hC;
          have : Λ ⊢! (⋀(Γ.erase p) ⋏ p) ⟶ q := by sorry;
          have : Λ ⊢! ⋀(Γ.erase p) ⟶ (p ⟶ q) := andImplyIffImplyImply'!.mp this;
          have : Λ ⊢! ⋀(Γ.erase p) ⟶ ⋁{p ⟶ q} := implyRightFinsetSingletonDisj!.mpr this
          have : Λ ⊬! ⋀(Γ.erase p) ⟶ ⋁{p ⟶ q} := t.consistent (by simp_all) (by simpa using h);
          contradiction;
      obtain ⟨t', ⟨⟨_, _⟩, _⟩⟩ := by simpa [Set.insert_subset_iff] using SaturatedConsistentTableau.lindenbaum this;
      existsi t';
      simp_all;
      apply t'.mem_either₁.mpr;
      simpa
    . simp [Satisfies.imp_def];
      intro h t' htt' hp;
      replace hp := ihp.mp hp;
      have hpq := htt' h;
      apply ihq.mpr;
      apply t'.mem_either₂.mp;
      exact SaturatedConsistentTableau.not_mem₂
        (show ↑({p, p ⟶ q} : Finset _) ⊆ t'.tableau.1 by simp_all;)
        (by
          apply implyLeftFinsetDoubletonConj!.mpr;
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
    simp only [Tableau.Consistent];
    rintro Γ Δ hΓ hΔ;
    replace hΓ := Set.eq_empty_of_subset_empty hΓ;
    replace hΔ := Set.subset_singleton_iff_eq.mp hΔ;
    simp_all only [Finset.coe_eq_empty, Finset.coe_eq_singleton]
    by_contra hC;
    cases hΔ with
    | inl h =>
      subst h;
      simp [Finset.conj, Finset.disj] at hC;
      have : Λ ⊢! p := efq'! $ hC ⨀ verum!
      contradiction;
    | inr h =>
      subst h;
      simp [Finset.conj, Finset.disj] at hC;
      have : Λ ⊢! p := disj₃'! (by simp) efq! $ hC ⨀ verum!;
      contradiction;
  obtain ⟨t', ht'⟩ := SaturatedConsistentTableau.lindenbaum this;
  simp [ValidOnModel.iff_models, ValidOnModel]
  existsi t';
  apply truthlemma.not.mpr;
  apply t'.mem_either₁.mpr;
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

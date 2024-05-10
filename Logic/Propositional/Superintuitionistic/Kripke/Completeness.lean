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
variable {p q r : F} {Γ Δ : Finset F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

lemma implyRightFinsetDoubletonDisj.mp [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ (⋁{q, r})) : (𝓢 ⊢ p ⟶ q ⋎ r) := by sorry;

lemma implyRightFinsetDoubletonDisj.mpr [HasEFQ 𝓢] (h : 𝓢 ⊢ p ⟶ q ⋎ r) : (𝓢 ⊢ p ⟶ (⋁{q, r})) := by sorry;

lemma implyRightFinsetDoubletonDisj! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ (⋁{q, r})) ↔ (𝓢 ⊢! p ⟶ q ⋎ r) := by
  constructor;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetDoubletonDisj.mp h⟩;
  . rintro ⟨h⟩; exact ⟨implyRightFinsetDoubletonDisj.mpr h⟩;

lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! Γ.conj) ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ
  case nil => simp;
  case cons p Δ ih =>
    simp;
    constructor
    · intro h; exact ⟨conj₁'! h, ih.mp (conj₂'! h)⟩
    · intro h; exact conj₃'! h.1 (ih.mpr h.2)

lemma iff_provable_finset_conj : (𝓢 ⊢! ⋀Γ) ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by simp [Finset.conj, iff_provable_list_conj]

/-
lemma list_disj_iff! {Γ : List F} [HasEFQ 𝓢] : (𝓢 ⊢! Γ.disj) ↔ (𝓢 ⊢! ⊥ ∨ ∃ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ
  case nil => simp only [List.disj_nil, List.not_mem_nil, false_and, exists_const, or_false];
  case cons p Δ ih =>
    simp_all only [List.disj_cons, List.mem_cons, exists_eq_or_imp];
    constructor
    · intro h;
      right;
    · rintro (h₁ | h₂ | h₃);
      . exact efq'! h₁;
      . exact disj₁'! h₂;
      . apply disj₂'!
        apply ih.mpr;
        right
        exact h₃;
-/

/-
lemma list_disj_iff_consistent! {Γ : List F} [HasEFQ 𝓢] (hc : 𝓢 ⊬! ⊥) : (𝓢 ⊢! Γ.disj) ↔ (∃ p ∈ Γ, 𝓢 ⊢! p) := by
  constructor;
  . intro h; exact or_iff_not_imp_left.mp (list_disj_iff!.mp h) hc;
  . intro h; apply list_disj_iff!.mpr; right; assumption

lemma finset_disj_iff! [HasEFQ 𝓢] : (𝓢 ⊢! ⋁Γ) ↔ (𝓢 ⊢! ⊥ ∨ ∃ p ∈ Γ, 𝓢 ⊢! p) := by
  simp [Finset.disj, list_disj_iff!]

lemma finset_disj_iff_consistent! [HasEFQ 𝓢] (hc : 𝓢 ⊬! ⊥) : (𝓢 ⊢! ⋁Γ) ↔ (∃ p ∈ Γ, 𝓢 ⊢! p) := by
  simp [Finset.disj, (list_disj_iff_consistent! hc)]
-/

lemma iffConjUnionFinset'! : 𝓢 ⊢! ⋀(Γ ∪ Δ) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    have h₁ := iff_provable_finset_conj.mp h;
    exact conj₃'!
      (by apply iff_provable_finset_conj.mpr; intro p hp; exact h₁ p (by simp [hp]))
      (by apply iff_provable_finset_conj.mpr; intro p hp; exact h₁ p (by simp [hp]));
  . intro h;
    have := iff_provable_finset_conj.mp $ conj₁'! h;
    have := iff_provable_finset_conj.mp $ conj₂'! h;
    apply iff_provable_finset_conj.mpr;
    intro q hq;
    cases Finset.mem_union.mp hq <;> simp_all;

lemma iffConjUnionFinset! : 𝓢 ⊢! ⋀(Γ ∪ Δ) ⟷ ⋀Γ ⋏ ⋀Δ := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjUnionFinset'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjUnionFinset'!.mpr;
    exact by_axm! (by simp);

lemma iffDisjUnionFinset'! : 𝓢 ⊢! ⋁(Γ ∪ Δ) ↔ 𝓢 ⊢! ⋁Γ ⋎ ⋁Δ := by sorry
  /-
  constructor;
  . intro h;
    have h₁ := iff_provable_finset_conj.mp h;
    exact disj₃'!
      (by apply iff_provable_finset_conj.mpr; intro p hp; exact h₁ p (by simp [hp]))
      (by apply iff_provable_finset_conj.mpr; intro p hp; exact h₁ p (by simp [hp]));
  . intro h;
    sorry;
  -/

lemma iffFinsetConjSingleton'! : (𝓢 ⊢! ⋀{p}) ↔ (𝓢 ⊢! p) := by
  constructor;
  . intro h; exact iff_provable_finset_conj.mp h p (by simp);
  . intro h; apply iff_provable_finset_conj.mpr; simpa;

@[simp]
lemma iffFinsetConjSingleton! : 𝓢 ⊢! ⋀{p} ⟷ p := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetConjSingleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetConjSingleton'!.mpr;
    exact by_axm! (by simp);

lemma iffConjInsertFinset'! : 𝓢 ⊢! ⋀(insert p Γ) ↔ 𝓢 ⊢! ⋀Γ ⋏ p := by
  have H : 𝓢 ⊢! ⋀(Γ ∪ {p}) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀{p} := iffConjUnionFinset'!
  constructor;
  . intro h;
    have e : Γ ∪ {p} = insert p Γ := by aesop;
    have hc := H.mp (by simpa [e] using h);
    exact conj₃'! (conj₁'! hc) (by apply iffFinsetConjSingleton'!.mp; exact conj₂'! hc);
  . intro h;
    apply iff_provable_finset_conj.mpr;
    intro q hq;
    cases (Finset.mem_insert.mp hq) with
    | inl t => subst t; exact conj₂'! h;
    | inr t => exact iff_provable_finset_conj.mp (conj₁'! h) _ t;

lemma iffConjInsertFinset! : 𝓢 ⊢! ⋀(insert p Γ) ⟷ ⋀Γ ⋏ p := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjInsertFinset'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjInsertFinset'!.mpr;
    exact by_axm! (by simp);

lemma iffFinsetConjDoubleton'! : 𝓢 ⊢! ⋀({p, q}) ↔ 𝓢 ⊢! p ⋏ q := by
  have : 𝓢 ⊢! ⋀({p, q}) ↔ 𝓢 ⊢! ⋀{q} ⋏ p := iffConjInsertFinset'!;
  have : 𝓢 ⊢! ⋀{q} ⋏ p ↔ 𝓢 ⊢! p ⋏ q := by
    constructor;
    . intro h;
      exact conj₃'! (conj₂'! h) (by apply iffFinsetConjSingleton'!.mp; exact conj₁'! h);
    . intro h;
      exact conj₃'! (by apply iffFinsetConjSingleton'!.mpr; exact conj₂'! h) (conj₁'! h);
  simp_all;

lemma iffFinsetConjDoubleton! : 𝓢 ⊢! ⋀({p, q}) ⟷ p ⋏ q := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetConjDoubleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetConjDoubleton'!.mpr;
    exact by_axm! (by simp);

lemma implyLeftReplaceIff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  constructor;
  . exact imp_trans! $ conj₂'! h;
  . exact imp_trans! $ conj₁'! h;

lemma implyRightReplaceIff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  constructor;
  . intro hrp; exact imp_trans! hrp $ conj₁'! h;
  . intro hrq; exact imp_trans! hrq $ conj₂'! h;

lemma implyLeftConjSingleton! : (𝓢 ⊢! (⋀{p}) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := implyLeftReplaceIff! iffFinsetConjSingleton!

lemma implyRightConjSingleton! : (𝓢 ⊢! p ⟶ (⋀{q})) ↔ (𝓢 ⊢! p ⟶ q) := implyRightReplaceIff! iffFinsetConjSingleton!

lemma implyLeftConjDoubleton! : (𝓢 ⊢! (⋀{p, q}) ⟶ r) ↔ (𝓢 ⊢! (p ⋏ q) ⟶ r) := implyLeftReplaceIff! iffFinsetConjDoubleton!

lemma implyRightConjDoubleton! : (𝓢 ⊢! r ⟶ (⋀{p, q})) ↔ (𝓢 ⊢! r ⟶ (p ⋏ q)) := implyRightReplaceIff! iffFinsetConjDoubleton!


lemma iffFinsetDisjSingleton'! [HasEFQ 𝓢] : (𝓢 ⊢! ⋁{p}) ↔ (𝓢 ⊢! p) := by
  simp [Finset.disj];
  constructor;
  . intro h; exact disj₃'! (by simp) efq! h;
  . intro h; exact disj₁'! h;

lemma iffFinsetDisjSingleton! [HasEFQ 𝓢] : 𝓢 ⊢! ⋁{p} ⟷ p := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetDisjSingleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffFinsetDisjSingleton'!.mpr;
    exact by_axm! (by simp);

lemma implyRightFinsetSingletonDisj! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ (⋁{q})) ↔ (𝓢 ⊢! p ⟶ q) := implyRightReplaceIff! iffFinsetDisjSingleton!

lemma implyLeftFinsetSingletonDisj'! [HasEFQ 𝓢] : (𝓢 ⊢! (⋁{p}) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := implyLeftReplaceIff! iffFinsetDisjSingleton!

  -- constructor;
  -- . rintro ⟨h⟩; exact ⟨implyRightFinsetSingletonDisj.mp h⟩;
  -- . rintro ⟨h⟩; exact ⟨implyRightFinsetSingletonDisj.mpr h⟩;

/-
lemma or_assoc'! : 𝓢 ⊢! p ⋎ (q ⋎ r) ↔ 𝓢 ⊢! (p ⋎ q) ⋎ r := by sorry;

lemma iffListDisjDoubleton'! [HasEFQ 𝓢] : (𝓢 ⊢! [p, q].disj) ↔ (𝓢 ⊢! p ⋎ q) := by
  simp [Finset.disj];
  constructor;
  . intro h; exact disj₃'! (by simp) efq! (or_assoc'!.mp h);
  . intro h; apply or_assoc'!.mpr; exact disj₁'! h;

lemma iffDisjDoubleton'! [HasEFQ 𝓢] : (𝓢 ⊢! ⋁{p, q}) ↔ (𝓢 ⊢! p ⋎ q) := by
  simp [Finset.disj, iffListDisjDoubleton'!];
  constructor;
  . intro h; exact disj₃'! (by simp) efq! (or_assoc'!.mp h);
  . intro h; exact disj₁'! h;
-/

lemma andRightImplyLeft'! (hpr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! (p ⋏ q) ⟶ r := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  replace hpr : [p ⋏ q] ⊢[𝓢]! p ⟶ r := weakening! (by simp) $ provable_iff_provable.mp hpr;
  have hpq : [p ⋏ q] ⊢[𝓢]! p ⋏ q := by_axm! (by simp);
  have hp : [p ⋏ q] ⊢[𝓢]! p := conj₁'! hpq;
  exact hpr ⨀ hp;

lemma andRightImplyLeft! : 𝓢 ⊢! (p ⟶ r) ⟶ ((p ⋏ q) ⟶ r) := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply andRightImplyLeft'!;
  exact by_axm! (by simp);

@[simp]
lemma forthbackConjErase : 𝓢 ⊢! ⋀Finset.erase Γ p ⋏ p ⟶ ⋀Γ := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have d : [⋀Finset.erase Γ p ⋏ p] ⊢[𝓢]! (⋀Finset.erase Γ p ⋏ p) := by_axm! (by simp);
  apply iff_provable_finset_conj.mpr;
  intro q hq;
  by_cases e : q = p;
  . subst e; exact conj₂'! d;
  . exact iff_provable_finset_conj.mp (conj₁'! d) q (by simp_all);

lemma implyLeftEraseConj (hC : 𝓢 ⊢! ⋀Γ ⟶ q) : 𝓢 ⊢! ⋀(Γ.erase p) ⋏ p ⟶ q := by
  exact imp_trans! (by simp) hC;

@[simp]
lemma disjinsert_list (Γ : List F) : 𝓢 ⊢! List.disj (p :: Γ) ↔ 𝓢 ⊢! p ⋎ Γ.disj := by simp;

@[simp]
lemma disjinsert : 𝓢 ⊢! ⋁(insert p Γ) ↔ 𝓢 ⊢! p ⋎ ⋁Γ := by sorry;

@[simp]
lemma forthbackDisjErase : 𝓢 ⊢! ⋁Γ ⟶ p ⋎ ⋁(Γ.erase p) := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have d : [⋁Γ] ⊢[𝓢]! ⋁Γ := by_axm! (by simp);
  by_cases h : p ∈ Γ;
  . have e := Finset.insert_erase h;
    nth_rw 2 [←(Finset.insert_erase h)] at d;
    exact disjinsert.mp d;
  . rw [Finset.erase_eq_of_not_mem h];
    exact disj₂'! d;

lemma implyRightEraseDisj (hC : 𝓢 ⊢! q ⟶ ⋁Γ) : 𝓢 ⊢! q ⟶ ⋁(Γ.erase p) ⋎ p := by
  exact imp_trans! hC $ imp_trans! (by simp) orComm!;

lemma orRightImplyRight'! (hpr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ (r ⋎ q) := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  replace hpr : [p] ⊢[𝓢]! p ⟶ r := weakening! (by simp) $ provable_iff_provable.mp hpr;
  have hp : [p] ⊢[𝓢]! p := by_axm! (by simp);
  exact disj₁'! (hpr ⨀ hp);


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

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ {Γ Δ}, ↑Γ ⊆ t.1 → ↑Δ ⊆ t.2 → Λ ⊬! ⋀Γ ⟶ ⋁Δ

variable (hCon : Consistent Λ t)

def consistent_either (p : Formula α) : Consistent Λ (insert p t.1, t.2) ∨ Consistent Λ (t.1, insert p t.2) := by
  by_contra hC;
  obtain ⟨⟨Γ₁, hΓ₁, Δ₁, hΔ₁, hC₁⟩, ⟨Γ₂, hΓ₂, Δ₂, hΔ₂, hC₂⟩⟩ := by simpa only [Consistent, not_or, not_forall, not_not, exists_prop, exists_and_left] using hC;
  replace hC₁ : Λ ⊢! ⋀(Γ₁.erase p) ⋏ p ⟶ ⋁Δ₁ := implyLeftEraseConj hC₁;
  replace hC₂ : Λ ⊢! ⋀Γ₂ ⟶ ⋁(Δ₂.erase p) ⋎ p := implyRightEraseDisj hC₂;
  -- have : Λ ⊢! ⋀(Γ₁.erase p) ⋏ p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂) := imp_trans! hC₁ (by simp)
  -- have : Λ ⊢! ⋀(Γ₁.erase p) ⟶ (p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂)) := andImplyIffImplyImply'!.mp this;
  sorry;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₂, hp₁, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [Consistent] at hCon;
  have : Λ ⊬! ⋀{p} ⟶ ⋁{p} := hCon
    (by simp_all; apply hp₁; simp_all only)
    (by simp_all; apply hp₂; simp_all only);
  have : Λ ⊢! ⋀{p} ⟶ ⋁{p} := by
    simp [Finset.conj, Finset.disj];
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    have : [p ⋏ ⊤] ⊢[Λ]! p ⋏ ⊤ := by_axm! (by simp only [List.mem_singleton]);
    exact disj₁'! $ conj₁'! this;
  contradiction;

lemma not_mem₂ {Γ : Finset (Formula α)} (hΓ : ↑Γ ⊆ t.1) (h : Λ ⊢! ⋀Γ ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! ⋀Γ ⟶ ⋁{q} := implyRightFinsetSingletonDisj!.mpr h;
  have : Λ ⊬! ⋀Γ ⟶ ⋁{q} := hCon (by simp_all only) (by simp_all only [Finset.coe_singleton, Set.singleton_subset_iff]);
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
    (by apply implyLeftConjSingleton!.mpr; simpa)

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
      apply implyLeftConjDoubleton!.mpr;
      apply implyRightFinsetSingletonDisj!.mpr;
      apply imp_id!;
    have : Λ ⊬! (⋀{p, q}) ⟶ (⋁{p ⋏ q}) := t.consistent
      (by simp_all only [Finset.coe_insert, Finset.coe_singleton, Set.subset_doubleton, and_self])
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
      apply implyLeftConjSingleton!.mpr;
      apply implyRightFinsetDoubletonDisj!.mpr;
      simp;
    have : Λ ⊬! ⋀{(p ⋎ q)} ⟶  ⋁{p, q} := t.consistent (by simp_all) (by simp_all);
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
      replace h := t.mem_either₁.mp h;
      have : Tableau.Consistent Λ (insert p t.tableau.1, {q}) := by
        simp only [Tableau.Consistent];
        intro Γ Δ hΓ hΔ;
        -- replace hΓ : ↑(Finset.erase Γ p) ⊆ t.tableau.1 := by simpa using hΓ;
        replace hΔ : Δ = ∅ ∨ Δ = {q} := by simpa using Set.subset_singleton_iff_eq.mp hΔ;
        by_contra hC;
        have : Λ ⊢! ⋀(Γ.erase p) ⟶ (p ⟶ q) := by
          cases hΔ with
          | inl h =>
            subst h;
            simp [Finset.disj] at hC;
            have : Λ ⊢! (⋀(Γ.erase p) ⋏ p) ⟶ ⊥ := implyLeftEraseConj hC;
            have : Λ ⊢! ⋀(Γ.erase p) ⟶ (p ⟶ ⊥) := andImplyIffImplyImply'!.mp this;
            exact imp_trans! this (by
              apply provable_iff_provable.mpr;
              apply deduct_iff.mpr;
              apply deduct_iff.mpr;
              have d₁ : [p, p ⟶ ⊥] ⊢[Λ]! p := by_axm! (by simp);
              have d₂ : [p, p ⟶ ⊥] ⊢[Λ]! p ⟶ ⊥ := by_axm! (by simp);
              exact efq'! $ d₂ ⨀ d₁;
            );
          | inr h =>
            subst h;
            simp [implyRightFinsetSingletonDisj!] at hC;
            have : Λ ⊢! (⋀(Γ.erase p) ⋏ p) ⟶ q := implyLeftEraseConj hC;
            exact andImplyIffImplyImply'!.mp this;
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
          apply implyLeftConjDoubleton!.mpr;
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

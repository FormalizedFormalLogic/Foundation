module

public import Foundation.Propositional.Formula.Basic
public import Foundation.Propositional.Entailment.Cl.Basic
public import Foundation.Vorspiel.Set.Basic
public import Foundation.Propositional.Entailment.Corsi

@[expose] public section

namespace LO.Propositional

open Entailment
open Formula

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

structure Tableau (α : Type u) where
  Γ : Set (Formula α)
  Δ : Set (Formula α)

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.Γ ⊆ t₂.Γ ∧ t₁.Δ ⊆ t₂.Δ⟩

def insert₁ (φ : Formula α) (t : Tableau α) : Tableau α := ⟨insert φ t.Γ, t.Δ⟩
def insert₂ (φ : Formula α) (t : Tableau α) : Tableau α := ⟨t.Γ, insert φ t.Δ⟩

variable {φ ψ: Formula α} {T U : FormulaSet α} {t u : Tableau α}

@[grind]
def Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ t.Γ) → (↑Δ ⊆ t.Δ) → 𝓢 ⊬ (Γ.conj) 🡒 (Δ.disj)

abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬Consistent 𝓢 t
lemma iff_inconsistent : Inconsistent 𝓢 t ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ t.Γ) ∧ (↑Δ ⊆ t.Δ) ∧ 𝓢 ⊢ (Γ.conj) 🡒 (Δ.disj) := by grind;

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.Γ ⊆ t₂.Γ ∧ t₁.Δ ⊆ t₂.Δ := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.Γ = t₂.Γ ∧ t₁.Δ = t₂.Δ := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma not_mem₂ (hCon : t.Consistent 𝓢) {Γ : Finset (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.Γ) (h : 𝓢 ⊢ Γ.conj 🡒 ψ) : ψ ∉ t.Δ := by
  by_contra hC;
  have : 𝓢 ⊢ Γ.conj 🡒 (Finset.disj {ψ}) := by simpa;
  have : 𝓢 ⊬ Γ.conj 🡒 (Finset.disj {ψ}) := hCon (by aesop) (by aesop);
  contradiction;

section

variable [Entailment.VF 𝓢]
open Entailment.Corsi

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : Disjoint t.Γ t.Δ := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨φ, hp⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hp;
  have : 𝓢 ⊬ (Finset.conj {φ}) 🡒 (Finset.disj {φ}) := hCon (by grind) (by grind);
  replace this : 𝓢 ⊬ φ 🡒 φ := by simpa using this;
  have : 𝓢 ⊢ φ 🡒 φ := impId;
  contradiction;

variable [DecidableEq α]

lemma iff_consistent_insert₁
  : (t.insert₁ φ).Consistent 𝓢 ↔ ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ t.Γ) → (↑Δ ⊆ t.Δ) → 𝓢 ⊬ (insert φ Γ).conj 🡒 Δ.disj := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := insert φ Γ) (Δ := Δ) ?_ hΔ;
    . assumption;
    . simp only [Finset.coe_insert];
      apply Set.insert_subset_insert;
      exact hΓ;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := Γ.erase φ) (Δ := Δ) (by simpa) hΔ;
    exact ruleI (CFConjFConj_of_subset (by grind)) hC;

lemma iff_not_consistent_insert₁ : (t.insert₁ φ).Inconsistent 𝓢  ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ t.Γ) ∧ (↑Δ ⊆ t.Δ) ∧ 𝓢 ⊢ (insert φ Γ).conj 🡒 Δ.disj := by
  apply Iff.trans iff_consistent_insert₁.not
  grind;

lemma iff_consistent_insert₂ : (t.insert₂ φ).Consistent 𝓢 ↔ ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ t.Γ) → (↑Δ ⊆ t.Δ) → 𝓢 ⊬ Γ.conj 🡒 (insert φ Δ).disj := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := Γ) (Δ := insert φ Δ) hΓ ?_;
    . assumption;
    . simp only [Finset.coe_insert];
      apply Set.insert_subset_insert;
      exact hΔ;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := Γ) (Δ := Δ.erase φ) hΓ (by simpa);
    apply ruleI hC;
    apply CFDisjFDisj_of_subset;
    grind;

lemma iff_not_consistent_insert₂ : (t.insert₂ φ).Inconsistent 𝓢  ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ t.Γ) ∧ (↑Δ ⊆ t.Δ) ∧ 𝓢 ⊢ Γ.conj 🡒 (insert φ Δ).disj := by
  apply Iff.trans iff_consistent_insert₂.not;
  grind;

section Consistent

variable {t : Tableau α}

lemma consistent_either (hCon : t.Consistent 𝓢) (φ : Formula α)
  : Tableau.Consistent 𝓢 (t.insert₁ φ) ∨ Tableau.Consistent 𝓢 (t.insert₂ φ) := by
  by_contra! hC;
  have ⟨h₁, h₂⟩ := hC;
  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_consistent_insert₁.mp h₁;
  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp h₂;
  apply @hCon (Γ := Γ₁ ∪ Γ₂) (Δ := Δ₁ ∪ Δ₂) ?_ ?_;
  . replace h₁ : 𝓢 ⊢ φ ⋏ Γ₁.conj 🡒 Δ₁.disj := ruleI insert_FConj h₁;
    replace h₂ : 𝓢 ⊢ Γ₂.conj 🡒 φ ⋎ Δ₂.disj := by
      apply ruleI;
      . exact h₂;
      . sorry;
    sorry;
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;

end Consistent

end


@[grind]
def Saturated (t : Tableau α) := ∀ φ : Formula α, φ ∈ t.Γ ∨ φ ∈ t.Δ

section Saturated

variable [Entailment.VF 𝓢]
variable {t : Tableau α}

lemma mem₂_of_notMem₁_of_saturated (hMat : Saturated t) : φ ∉ t.Γ → φ ∈ t.Δ := by grind;
lemma mem₁_of_notMem₂_of_saturated (hMat : Saturated t) : φ ∉ t.Δ → φ ∈ t.Γ := by grind;

@[grind .]
lemma iff_mem₁_notMem₂_of_consistent_saturated (hCon : t.Consistent 𝓢) (hSat : Saturated t) : φ ∈ t.Γ ↔ φ ∉ t.Δ := by
  constructor;
  . apply Set.disjoint_right.mp $ Disjoint.symm $ disjoint_of_consistent hCon;
  . apply mem₁_of_notMem₂_of_saturated hSat;

@[grind .]
lemma iff_mem₂_notMem₁_of_consistent_saturated (hCon : t.Consistent 𝓢) (hSat : Saturated t) : φ ∈ t.Δ ↔ φ ∉ t.Γ := by
  constructor;
  . apply Set.disjoint_left.mp $ Disjoint.symm $ disjoint_of_consistent hCon;
  . apply mem₂_of_notMem₁_of_saturated hSat;

lemma saturated_duality {t₁ t₂ : Tableau α} (ct₁ : t₁.Consistent 𝓢) (ct₂ : t₂.Consistent 𝓢) (st₁ : Saturated t₁) (st₂ : Saturated t₂) :
  t₁.Γ = t₂.Γ ↔ t₁.Δ = t₂.Δ := by grind;

end Saturated

lemma emptyset_consistent [Entailment.VF 𝓢] [DecidableEq α] [H_consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ⟨∅, ∅⟩ := by
  intro Γ Δ hΓ hΔ;
  by_contra hC;
  obtain ⟨ψ, hψ⟩ := H_consis.exists_unprovable;
  apply hψ;
  simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ;
  subst hΓ hΔ;
  simp only [Finset.conj_empty, Finset.disj_empty] at hC;
  exact Corsi.of_O (hC ⨀ (by simp));

section lindenbaum

variable (𝓢 : S)
variable {t : Tableau α}

open Classical
open Encodable

noncomputable def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent 𝓢 (t.insert₁ φ) then (t.insert₁ φ) else (t.insert₂ φ)

noncomputable def lindenbaum_next_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some φ => (lindenbaum_next_indexed t i).lindenbaum_next 𝓢 φ
    | none => lindenbaum_next_indexed t i
local notation:max t"[" i "]" => lindenbaum_next_indexed 𝓢 t i

def lindenbaum_maximal [Encodable α] (t : Tableau α) : Tableau α := ⟨⋃ i, t[i].1, ⋃ i, t[i].2⟩
local notation:max t"∞" => lindenbaum_maximal 𝓢 t

@[simp] lemma lindenbaum_next_indexed_zero [Encodable α] {t : Tableau α} : (t.lindenbaum_next_indexed 𝓢 0) = t := by simp [lindenbaum_next_indexed]

variable {𝓢}

lemma next_parametericConsistent [Entailment.VF 𝓢] (consistent : t.Consistent 𝓢) (φ : Formula α) : (t.lindenbaum_next 𝓢 φ).Consistent 𝓢 := by
  dsimp [lindenbaum_next];
  split;
  . simpa;
  . rcases (consistent_either consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma lindenbaum_next_indexed_parametricConsistent_succ [Entailment.VF 𝓢] {i : ℕ} : Consistent 𝓢 t[i] → Consistent 𝓢 t[i + 1] := by
  dsimp [lindenbaum_next_indexed];
  split;
  . intro h;
    apply next_parametericConsistent (𝓢 := 𝓢);
    assumption;
  . tauto;

lemma mem_lindenbaum_next_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp only [lindenbaum_next_indexed, encodek, lindenbaum_next];
  split;
  . left; tauto;
  . right; tauto;

lemma lindenbaum_next_indexed_parametricConsistent [Entailment.VF 𝓢] (consistent : t.Consistent 𝓢) (i : ℕ) : t[i].Consistent 𝓢 := by
  induction i with
  | zero => simpa;
  | succ i ih => apply lindenbaum_next_indexed_parametricConsistent_succ; assumption;

variable {m n : ℕ}

lemma lindenbaum_next_indexed_subset₁_of_lt (h : m ≤ n) : t[m].1 ⊆ t[n].1 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_next_indexed, lindenbaum_next];
    split;
    . split <;> tauto;
    . tauto;

lemma lindenbaum_next_indexed_subset₂_of_lt (h : m ≤ n) : t[m].2 ⊆ t[n].2 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_next_indexed, lindenbaum_next];
    split;
    . split <;> tauto;
    . tauto;

lemma exists_list_lindenbaum_index₁ {Γ : List _} (hΓ : ↑Γ.toFinset ⊆ ⋃ i, t[i].1): ∃ m, ∀ φ ∈ Γ, φ ∈ t[m].1 := by
  induction Γ with
  | nil => simp;
  | cons φ Γ ih =>
    simp_all only [List.coe_toFinset, List.toFinset_cons, Finset.coe_insert, List.mem_cons, forall_eq_or_imp];
    replace hΓ := Set.insert_subset_iff.mp hΓ;
    obtain ⟨_, ⟨i, _⟩, _⟩ := hΓ.1;
    obtain ⟨m, hm⟩ := ih hΓ.2;
    use (i + m);
    constructor;
    . apply lindenbaum_next_indexed_subset₁_of_lt (m := i);
      . omega;
      . simp_all;
    . intro ψ hq;
      exact lindenbaum_next_indexed_subset₁_of_lt (by simp) $ hm ψ hq;

lemma exists_finset_lindenbaum_index₁ {Γ : Finset _} (hΓ : ↑Γ ⊆ ⋃ i, t[i].1): ∃ m, ∀ φ ∈ Γ, φ ∈ t[m].1 := by
  obtain ⟨m, hΓ⟩ := exists_list_lindenbaum_index₁ (Γ := Γ.toList) (t := t) (by simpa);
  use m;
  intro φ hφ;
  apply hΓ;
  simpa;

lemma exists_list_lindenbaum_index₂ {Δ : List _} (hΔ : ↑Δ.toFinset ⊆ ⋃ i, t[i].2) : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
  induction Δ with
  | nil => simp;
  | cons φ Δ ih =>
    simp_all only [List.coe_toFinset, List.toFinset_cons, Finset.coe_insert, List.mem_cons, forall_eq_or_imp];
    replace hΔ := Set.insert_subset_iff.mp hΔ;
    obtain ⟨_, ⟨i, _⟩, _⟩ := hΔ.1;
    obtain ⟨n, hn⟩ := ih hΔ.2;
    use (i + n);
    constructor;
    . apply lindenbaum_next_indexed_subset₂_of_lt (m := i);
      . omega;
      . simp_all
    . intro ψ hq;
      exact lindenbaum_next_indexed_subset₂_of_lt (by simp) $ hn ψ hq;

lemma exists_finset_lindenbaum_index₂ {Δ : Finset _} (hΓ : ↑Δ ⊆ ⋃ i, t[i].2) : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
  obtain ⟨m, hΔ⟩ := exists_list_lindenbaum_index₂ (Δ := Δ.toList) (𝓢 := 𝓢) (t := t) (by simpa);
  use m;
  intro φ hφ;
  apply hΔ;
  simpa;

lemma exists_parametricConsistent_saturated_tableau [Entailment.VF 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (Tableau.Consistent 𝓢 u) ∧ (Saturated u) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?saturated⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case saturated =>
    intro φ;
    simp only [lindenbaum_maximal, Set.mem_iUnion];
    rcases mem_lindenbaum_next_indexed (𝓢 := 𝓢) t φ with (h | h);
    . left; use (encode φ + 1);
    . right; use (encode φ + 1);
  case consistent =>
    intro Γ Δ hΓ hΔ;
    simp_all only [lindenbaum_maximal];
    obtain ⟨m, hΓ⟩ := exists_finset_lindenbaum_index₁ hΓ;
    obtain ⟨n, hΔ⟩ := exists_finset_lindenbaum_index₂ hΔ;
    rcases (lt_trichotomy m n) with hm | hmn | hn;
    . exact lindenbaum_next_indexed_parametricConsistent hCon n (by intro φ hp; exact lindenbaum_next_indexed_subset₁_of_lt hm.le $ hΓ φ (by simpa)) hΔ;
    . subst hmn;
      exact lindenbaum_next_indexed_parametricConsistent hCon m hΓ hΔ;
    . exact lindenbaum_next_indexed_parametricConsistent hCon m hΓ (by intro φ hp; exact lindenbaum_next_indexed_subset₂_of_lt hn.le $ hΔ φ hp);

protected alias lindenbaum := exists_parametricConsistent_saturated_tableau

end lindenbaum

end Tableau

open Tableau

@[ext]
structure SaturatedConsistentTableau (𝓢 : S) extends Tableau α where
  saturated : Saturated toTableau
  consistent : Consistent 𝓢 toTableau

namespace SaturatedConsistentTableau

variable {t₀ : Tableau α} {φ ψ : Formula α}

attribute [simp, grind .] saturated consistent

lemma lindenbaum [Entailment.VF 𝓢] [Encodable α] (hCon : t₀.Consistent 𝓢) : ∃ (t : SaturatedConsistentTableau 𝓢), t₀ ⊆ t.toTableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [Entailment.Consistent 𝓢] [Entailment.VF 𝓢] [DecidableEq α] [Encodable α] : Nonempty (SaturatedConsistentTableau 𝓢) := ⟨lindenbaum Tableau.emptyset_consistent |>.choose⟩

variable {t t₁ t₂ : SaturatedConsistentTableau 𝓢}

lemma not_mem₂ {Γ : Finset (Formula α)} (hΓ : ↑Γ ⊆ t.Γ) (h : 𝓢 ⊢ Γ.conj 🡒 ψ) : ψ ∉ t.Δ := t.toTableau.not_mem₂ t.consistent hΓ h

variable [Entailment.VF 𝓢]

@[simp, grind .] lemma disjoint : Disjoint t.Γ t.Δ := t.toTableau.disjoint_of_consistent t.consistent

lemma iff_mem₁_notMem₂ : φ ∈ t.Γ ↔ φ ∉ t.Δ := t.toTableau.iff_mem₁_notMem₂_of_consistent_saturated t.consistent t.saturated
lemma iff_mem₂_notMem₁ : φ ∈ t.Δ ↔ φ ∉ t.Γ := t.toTableau.iff_mem₂_notMem₁_of_consistent_saturated t.consistent t.saturated

attribute [grind =_] iff_mem₁_notMem₂ iff_mem₂_notMem₁

@[grind =] lemma saturated_duality: t₁.Γ = t₂.Γ ↔ t₁.Δ = t₂.Δ := Tableau.saturated_duality t₁.consistent t₂.consistent t₁.saturated t₂.saturated

@[grind <=] lemma equality_of₁ (e₁ : t₁.Γ = t₂.Γ) : t₁ = t₂ := by ext <;> grind;
@[grind <=] lemma equality_of₂ (e₂ : t₁.Δ = t₂.Δ) : t₁ = t₂ := by ext <;> grind;

/-
section

variable [DecidableEq α] [Encodable α]

lemma iff_provable_include₁ : T *⊢[𝓢] φ ↔ ∀ t : SaturatedConsistentTableau 𝓢, (T ⊆ t.1.1) → φ ∈ t.1.1 := by
  constructor;
  . intro h t hT;
    by_contra hφ;
    replace hφ := iff_not_mem₁_mem₂.mp hφ;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply t.consistent (Γ := Γ.toFinset) (Δ := {φ}) ?_ ?_;
    . apply FConj_DT.mpr;
      simpa using iff_FiniteContext_Context.mp hΓ₂;
    . intro ψ hψ;
      apply hT;
      apply hΓ₁;
      simpa using hψ;
    . simpa;
  . intro h;
    by_contra! hC;
    obtain ⟨t, ht⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨T, {φ}⟩) $ by
      intro Γ Δ hΓ hΔ;
      contrapose! hC;
      replace h : T *⊢[𝓢] Δ.disj := Context.weakening! (by simpa using hΓ) $ FConj_DT.mp hC;
      rcases Set.subset_singleton_iff_eq.mp hΔ with (hΔ | hΔ);
      . simp only [Finset.coe_eq_empty] at hΔ;
        subst hΔ;
        exact of_O! $ by simpa using h;
      . simp only [Finset.coe_eq_singleton] at hΔ;
        subst hΔ;
        simpa using h;
    apply iff_not_mem₂_mem₁.mpr $ h t ht.1;
    apply ht.2;
    simp;

lemma iff_provable_include₁_finset {Γ : Finset (Formula α)} : ↑Γ *⊢[𝓢] φ ↔ ∀ t : SaturatedConsistentTableau 𝓢, (↑Γ ⊆ t.1.1) → φ ∈ t.1.1 := iff_provable_include₁

lemma iff_provable_mem₁ : 𝓢 ⊢ φ ↔ ∀ t : SaturatedConsistentTableau 𝓢, φ ∈ t.1.1 := by
  constructor;
  . intro h t;
    apply iff_provable_include₁ (T := ∅) |>.mp;
    . exact Context.of! h;
    . simp;
  . intro h;
    exact Context.emptyPrf! $ iff_provable_include₁.mpr $ by tauto;

end
-/

section Saturated

lemma imp_closed₁ (h : 𝓢 ⊢ φ 🡒 ψ) (hp₁ : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  by_contra hq₂;
  apply t.consistent (Γ := {φ}) (Δ := {ψ});
  . grind;
  . grind;
  . simpa;

lemma imp_closed₂ (h : 𝓢 ⊢ φ 🡒 ψ) (hp₂ : ψ ∈ t.1.2) : φ ∈ t.1.2 := by
  contrapose! hp₂;
  grind [imp_closed₁ h];

@[simp, grind .]
lemma mem₁_verum : ⊤ ∈ t.Γ := by
  by_contra hC;
  apply t.consistent (Γ := ∅) (Δ := {⊤});
  . grind;
  . grind;
  . simp;

@[simp, grind .]
lemma notMem₁_falsum : ⊥ ∉ t.Γ := by
  by_contra hC;
  apply t.consistent (Γ := {⊥}) (Δ := ∅);
  . grind;
  . grind;
  . simp;

@[simp, grind .]
lemma mem₂_falsum : ⊥ ∈ t.Δ := by grind;

lemma mem₁_of_provable (t : SaturatedConsistentTableau 𝓢) : 𝓢 ⊢ φ → φ ∈ t.Γ := by
  intro h;
  apply imp_closed₁ (φ := ⊤);
  . apply Corsi.af h;
  . grind;

open Entailment.Corsi

@[grind =>]
lemma iff_mem₁_and [DecidableEq α] : φ ⋏ ψ ∈ t.Γ ↔ φ ∈ t.Γ ∧ ψ ∈ t.Γ := by
  constructor;
  . intro h; constructor <;> exact imp_closed₁ (by simp) h
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    apply t.consistent (Γ := {φ, ψ}) (Δ := {φ ⋏ ψ});
    . grind;
    . grind;
    . rw [Finset.disj_singleton];
      apply ruleC <;> exact mem_fconj (by simp);

@[grind =>]
lemma iff_mem₂_and [DecidableEq α] : φ ⋏ ψ ∈ t.Δ ↔ φ ∈ t.Δ ∨ ψ ∈ t.Δ := by grind;

attribute [grind =] List.conj₂_nil List.conj₂_singleton List.conj₂_cons_nonempty

lemma iff_mem₁_conj₂ [DecidableEq α] {Γ : List (Formula α)} : ⋀Γ ∈ t.Γ ↔ ∀ φ ∈ Γ, φ ∈ t.Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ Γ_nil ih =>
    simp only [(List.conj₂_cons_nonempty Γ_nil), List.mem_cons];
    constructor;
    . rintro h φ (rfl | hp);
      . exact iff_mem₁_and.mp h |>.1;
      . exact ih.mp (iff_mem₁_and.mp h |>.2) _ hp;
    . intro h;
      apply iff_mem₁_and.mpr;
      grind;
  | _ => simp;

lemma iff_mem₁_fconj [DecidableEq α] {Γ : Finset (Formula α)} : Γ.conj ∈ t.Γ ↔ ↑Γ ⊆ t.Γ := by
  apply Iff.trans iff_mem₁_conj₂;
  grind [Finset.mem_toList];

@[grind =>]
lemma iff_mem₁_or [DecidableEq α] : φ ⋎ ψ ∈ t.Γ ↔ φ ∈ t.Γ ∨ ψ ∈ t.Γ := by
  constructor;
  . intro h;
    by_contra! hC;
    apply t.consistent (Γ := {φ ⋎ ψ}) (Δ := {φ, ψ}) (by simp_all);
    . grind;
    . rw [Finset.conj_singleton];
      apply ruleD <;> apply mem_fdisj (by simp);
  . rintro (h | h) <;> apply imp_closed₁ (by simp) h;

@[grind =>]
lemma iff_mem₂_or [DecidableEq α] : φ ⋎ ψ ∈ t.Δ ↔ φ ∈ t.Δ ∧ ψ ∈ t.Δ := by grind;

lemma iff_mem₂_disj [DecidableEq α] {Γ : List (Formula α)} : ⋁Γ ∈ t.1.2 ↔ ∀ φ ∈ Γ, φ ∈ t.1.2 := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ Γ_nil ih =>
    simp only [(List.disj₂_cons_nonempty Γ_nil), List.mem_cons];
    constructor;
    . rintro h φ (rfl | hp);
      . exact iff_mem₂_or.mp h |>.1;
      . exact ih.mp (iff_mem₂_or.mp h |>.2) _ hp;
    . intro h;
      apply iff_mem₂_or.mpr;
      simp_all;
  | _ => simp;

lemma iff_mem₂_fdisj [DecidableEq α] {Γ : Finset (Formula α)} : Γ.disj ∈ t.1.2 ↔ ↑Γ ⊆ t.1.2 := by
  apply Iff.trans iff_mem₂_disj;
  grind [Finset.mem_toList]

@[grind =>]
lemma of_mem₁_imp [DecidableEq α] [HasAxiomRfl 𝓢] (h : φ 🡒 ψ ∈ t.Γ) (hp : φ ∈ t.Γ) : ψ ∈ t.Γ := by
  by_contra hC;
  apply t.consistent (Γ := {φ, φ 🡒 ψ}) (Δ := {ψ});
  . grind;
  . grind;
  . rw [Finset.disj_singleton];
    apply ruleI (ψ := φ ⋏ (φ 🡒 ψ));
    . apply ruleC <;> exact mem_fconj (by simp);
    . simp;

lemma of_mem₁_imp' [DecidableEq α] [HasAxiomRfl 𝓢] : φ 🡒 ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by grind [of_mem₁_imp];


@[grind =>]
lemma of_mem₁_neg [DecidableEq α] [HasAxiomRfl 𝓢] (h : ∼φ ∈ t.1.1) : φ ∉ t.1.1 := by grind [of_mem₁_imp];

lemma of_mem₁_neg' [DecidableEq α] [HasAxiomRfl 𝓢] (h : ∼φ ∈ t.1.1) : φ ∈ t.1.2 := by grind;


private lemma of_mem₂_imp [DecidableEq α] [Encodable α] [HasAxiomRfl 𝓢] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  intro h;
  set_option push_neg.use_distrib true in by_contra! hC;
  rcases hC with (hφ | hψ);
  . rcases iff_mem₁_or.mp (mem₁_of_provable t (show 𝓢 ⊢ φ ⋎ (φ 🡒 ψ) by sorry)) with (_ | _) <;> grind;
  . exact (iff_mem₁_notMem₂.mp $ of_mem₁_imp (mem₁_of_provable t (by sorry)) $ iff_mem₁_notMem₂.mpr hψ) h;

lemma iff_mem₁_imp [DecidableEq α] [Encodable α] [HasAxiomRfl 𝓢] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.1 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  grind only [of_mem₁_imp, of_mem₂_imp, iff_mem₂_notMem₁, iff_mem₁_notMem₂];

lemma iff_mem₂_imp [DecidableEq α] [Encodable α] [HasAxiomRfl 𝓢] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.2 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  grind only [of_mem₁_imp, of_mem₂_imp, iff_mem₂_notMem₁, iff_mem₁_notMem₂];

end Saturated

end SaturatedConsistentTableau

end LO.Propositional
end

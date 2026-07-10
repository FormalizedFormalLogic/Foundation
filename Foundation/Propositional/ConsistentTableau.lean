module

public import Foundation.Propositional.Formula.Basic
public import Foundation.Propositional.Entailment.Cl.Basic
public import Foundation.Vorspiel.Set.Basic

@[expose] public section

namespace LO.Propositional

open Entailment FiniteContext
open Formula

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

def Tableau (α : Type u) := Set (Formula α) × Set (Formula α)

namespace Tableau

variable {φ ψ: Formula α} {T U : FormulaSet α} {t u : Tableau α}

abbrev Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ t.1) → (↑Δ ⊆ t.2) → 𝓢 ⊬ (Γ.conj) 🡒 (Δ.disj)

abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬Consistent 𝓢 t

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩
@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma not_mem₂ (hCon : t.Consistent 𝓢) {Γ : Finset (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1) (h : 𝓢 ⊢ Γ.conj 🡒 ψ) : ψ ∉ t.2 := by
  by_contra hC;
  have : 𝓢 ⊢ Γ.conj 🡒 (Finset.disj {ψ}) := by simpa;
  have : 𝓢 ⊬ Γ.conj 🡒 (Finset.disj {ψ}) := hCon (by aesop) (by aesop);
  contradiction;

section

variable [Entailment.Int 𝓢]

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨φ, hp⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hp;
  have : 𝓢 ⊬ (Finset.conj {φ}) 🡒 (Finset.disj {φ}) := hCon
    (by simp_all only [Finset.coe_singleton, Set.singleton_subset_iff]; apply hp₁; assumption)
    (by simp_all only [Finset.coe_singleton, Set.singleton_subset_iff]; apply hp₂; assumption);
  replace this : 𝓢 ⊬ φ 🡒 φ := by simpa using this;
  have : 𝓢 ⊢ φ 🡒 φ := C!_id;
  contradiction;

variable [DecidableEq α]

lemma iff_consistent_insert₁
  : Tableau.Consistent 𝓢 ((insert φ T), U) ↔ ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ T) → (↑Δ ⊆ U) → 𝓢 ⊬ φ ⋏ Γ.conj 🡒 Δ.disj := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := insert φ Γ) (Δ := Δ) ?_ hΔ;
    . exact C!_trans (by simp) hC;
    . simp only [Finset.coe_insert];
      apply Set.insert_subset_insert;
      exact hΓ;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    simp_all only;
    apply h (Γ := Γ.erase φ) (Δ := Δ) (by simpa) hΔ;
    refine C!_trans ?_ hC;
    . exact C!_trans CKFConjinsertFConj! $ CFConj_FConj!_of_subset $ Finset.insert_erase_subset φ Γ

lemma iff_not_consistent_insert₁ : ¬Tableau.Consistent 𝓢 ((insert φ T), U) ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ T) ∧ (↑Δ ⊆ U) ∧ 𝓢 ⊢ φ ⋏ Γ.conj 🡒 Δ.disj := by
  constructor;
  . contrapose!; apply iff_consistent_insert₁.mpr;
  . contrapose!; apply iff_consistent_insert₁.mp;

lemma iff_consistent_insert₂ : Tableau.Consistent 𝓢 (T, (insert φ U)) ↔ ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ T) → (↑Δ ⊆ U) → 𝓢 ⊬ Γ.conj 🡒 φ ⋎ Δ.disj := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := Γ) (Δ := insert φ Δ) hΓ ?_;
    . exact C!_trans hC $ by simp;
    . simp only [Finset.coe_insert];
      apply Set.insert_subset_insert;
      exact hΔ;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    apply h (Γ := Γ) (Δ := Δ.erase φ) hΓ (by simpa);
    exact C!_trans hC $ by
      refine C!_trans ?_ $ CinsertFDisjAFDisj! (𝓢 := 𝓢) (Γ := Δ.erase φ);
      apply CDisj₂Disj₂_of_subset;
      simp only [Finset.mem_toList, Finset.mem_insert, Finset.mem_erase, ne_eq];
      tauto;

lemma iff_not_consistent_insert₂ : ¬Tableau.Consistent 𝓢 (T, (insert φ U)) ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ T) ∧ (↑Δ ⊆ U) ∧ 𝓢 ⊢ Γ.conj 🡒 φ ⋎ Δ.disj := by
  constructor;
  . contrapose!; apply iff_consistent_insert₂.mpr;
  . contrapose!; apply iff_consistent_insert₂.mp;

section Consistent

variable {t : Tableau α}

lemma consistent_either (hCon : t.Consistent 𝓢) (φ : Formula α) : Tableau.Consistent 𝓢 ((insert φ t.1), t.2) ∨ Tableau.Consistent 𝓢 (t.1, (insert φ t.2)) := by
  by_contra hC;
  push Not at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_consistent_insert₁.mp hC₁;
  replace h₁ := left_K!_symm h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;
  apply @hCon (Γ := Γ₁ ∪ Γ₂) (Δ := Δ₁ ∪ Δ₂) ?_ ?_;
  . exact C!_trans (C!_trans (by simp) (cut! h₁ h₂)) (by simp);
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;

  -- have : 𝓢 ⊢ ⋀(Γ₁ ++ Γ₂) 🡒 ⋁(Δ₁ ++ Δ₂) := C!_trans (K!_left EConj₂AppendKConj₂Conj₂!) $ C!_trans (cut! h₁ h₂) (K!_right EDisj₂AppendADisj₂Disj₂!);

end Consistent

end

abbrev Saturated (t : Tableau α) := ∀ φ : Formula α, φ ∈ t.1 ∨ φ ∈ t.2

section Saturated

variable [Entailment.Int 𝓢]
variable {t : Tableau α}

lemma mem₂_of_not_mem₁ (hMat : Saturated t) : φ ∉ t.1 → φ ∈ t.2 := by
  intro h;
  cases (hMat φ) with
  | inl h' => exact absurd h' h;
  | inr _ => assumption;

lemma mem₁_of_not_mem₂ (hMat : Saturated t) : φ ∉ t.2 → φ ∈ t.1 := by
  intro h;
  cases (hMat φ) with
  | inl _ => assumption;
  | inr h' => exact absurd h' h;

lemma not_mem₁_iff_mem₂ (hCon : t.Consistent 𝓢) (hMat : Saturated t) : φ ∉ t.1 ↔ φ ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma not_mem₂_iff_mem₁ (hCon : t.Consistent 𝓢) (hMat : Saturated t) : φ ∉ t.2 ↔ φ ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hMat;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon;

lemma saturated_duality
  {t₁ t₂ : Tableau α}
  (ct₁ : t₁.Consistent 𝓢) (ct₂ : t₂.Consistent 𝓢)
  (st₁ : Saturated t₁) (st₂ : Saturated t₂)
  : t₁.1 = t₂.1 ↔ t₁.2 = t₂.2 := by
  constructor;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply not_mem₁_iff_mem₂ ct₂ st₂ |>.mp; rw [←h];
      apply not_mem₁_iff_mem₂ ct₁ st₁ |>.mpr hp;
    . intro φ hp;
      apply not_mem₁_iff_mem₂ ct₁ st₁ |>.mp; rw [h];
      apply not_mem₁_iff_mem₂ ct₂ st₂ |>.mpr hp;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply not_mem₂_iff_mem₁ ct₂ st₂ |>.mp; rw [←h];
      apply not_mem₂_iff_mem₁ ct₁ st₁ |>.mpr hp;
    . intro φ hp;
      apply not_mem₂_iff_mem₁ ct₁ st₁ |>.mp; rw [h];
      apply not_mem₂_iff_mem₁ ct₂ st₂ |>.mpr hp;

end Saturated

lemma emptyset_consistent [Entailment.Int 𝓢] [DecidableEq α] [H_consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ⟨∅, ∅⟩ := by
  intro Γ Δ hΓ hΔ;
  by_contra hC;
  obtain ⟨ψ, hψ⟩ := H_consis.exists_unprovable;
  apply hψ;
  simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ;
  subst hΓ hΔ;
  simp only [Finset.conj_empty, Finset.disj_empty] at hC;
  exact of_O! (hC ⨀ C!_id);

section lindenbaum

variable (𝓢 : S)
variable {t : Tableau α}

open Classical
open Encodable

noncomputable def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent 𝓢 (insert φ t.1, t.2) then (insert φ t.1, t.2) else (t.1, insert φ t.2)

noncomputable def lindenbaum_next_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some φ => (lindenbaum_next_indexed t i).lindenbaum_next 𝓢 φ
    | none => lindenbaum_next_indexed t i
local notation:max t"[" i "]" => lindenbaum_next_indexed 𝓢 t i

def lindenbaum_maximal [Encodable α] (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_maximal 𝓢 t

@[simp] lemma lindenbaum_next_indexed_zero [Encodable α] {t : Tableau α} : (t.lindenbaum_next_indexed 𝓢 0) = t := by simp [lindenbaum_next_indexed]

variable {𝓢}

lemma next_parametericConsistent [Entailment.Int 𝓢] (consistent : t.Consistent 𝓢) (φ : Formula α) : (t.lindenbaum_next 𝓢 φ).Consistent 𝓢 := by
  dsimp [lindenbaum_next];
  split;
  . simpa;
  . rcases (consistent_either consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma lindenbaum_next_indexed_parametricConsistent_succ [Entailment.Int 𝓢] {i : ℕ} : Consistent 𝓢 t[i] → Consistent 𝓢 t[i + 1] := by
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

lemma lindenbaum_next_indexed_parametricConsistent [Entailment.Int 𝓢] (consistent : t.Consistent 𝓢) (i : ℕ) : t[i].Consistent 𝓢 := by
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

lemma exists_finset_lindenbaum_index₁ {Γ : Finset _} (hΓ : (SetLike.coe Γ) ⊆ ⋃ i, t[i].1): ∃ m, ∀ φ ∈ Γ, φ ∈ t[m].1 := by
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

lemma exists_finset_lindenbaum_index₂ {Δ : Finset _} (hΓ : (SetLike.coe Δ) ⊆ ⋃ i, t[i].2) : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
  obtain ⟨m, hΔ⟩ := exists_list_lindenbaum_index₂ (Δ := Δ.toList) (𝓢 := 𝓢) (t := t) (by simpa);
  use m;
  intro φ hφ;
  apply hΔ;
  simpa;

lemma exists_parametricConsistent_saturated_tableau [Entailment.Int 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (Tableau.Consistent 𝓢 u) ∧ (Saturated u) := by
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

def SaturatedConsistentTableau (𝓢 : S) := {t : Tableau α // Saturated t ∧ t.Consistent 𝓢}

namespace SaturatedConsistentTableau

lemma consistent (t : SaturatedConsistentTableau 𝓢) : Consistent 𝓢 t.1 := t.2.2

lemma saturated (t : SaturatedConsistentTableau 𝓢) : Saturated t.1 := t.2.1

variable {t₀ : Tableau α} {φ ψ : Formula α}

lemma lindenbaum [Entailment.Int 𝓢] [Encodable α] (hCon : t₀.Consistent 𝓢) : ∃ (t : SaturatedConsistentTableau 𝓢), t₀ ⊆ t.1 := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [Entailment.Consistent 𝓢] [Entailment.Int 𝓢] [DecidableEq α] [Encodable α] : Nonempty (SaturatedConsistentTableau 𝓢) := ⟨lindenbaum Tableau.emptyset_consistent |>.choose⟩

variable {t t₁ t₂ : SaturatedConsistentTableau 𝓢}

lemma not_mem₂ {Γ : Finset (Formula α)} (hΓ : ↑Γ ⊆ t.1.1) (h : 𝓢 ⊢ Γ.conj 🡒 ψ) : ψ ∉ t.1.2 := t.1.not_mem₂ t.consistent hΓ h

variable [Entailment.Int 𝓢]

@[simp] lemma disjoint : Disjoint t.1.1 t.1.2 := t.1.disjoint_of_consistent t.2.2

lemma iff_not_mem₁_mem₂ : φ ∉ t.1.1 ↔ φ ∈ t.1.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma iff_not_mem₂_mem₁ : φ ∉ t.1.2 ↔ φ ∈ t.1.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

lemma saturated_duality: t₁.1.1 = t₂.1.1 ↔ t₁.1.2 = t₂.1.2 := Tableau.saturated_duality t₁.consistent t₂.consistent t₁.saturated t₂.saturated

lemma equality_of₁ (e₁ : t₁.1.1 = t₂.1.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (saturated_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.1, t₁.saturated, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.1, t₂.saturated, t₂.consistent⟩ := by simp [e];

lemma equality_of₂ (e₂ : t₁.1.2 = t₂.1.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂

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

section Saturated

lemma mdp_mem₁_provable (h : 𝓢 ⊢ φ 🡒 ψ) (hp₁ : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hq₂;
  apply by simpa using t.consistent (Γ := {φ}) (Δ := {ψ}) (by simpa) (by simpa);
  exact h;

lemma mdp_mem₂_provable (h : 𝓢 ⊢ φ 🡒 ψ) (hp₁ : ψ ∈ t.1.2) : φ ∈ t.1.2 := by
  by_contra hq₂;
  have := iff_not_mem₂_mem₁.mpr $ mdp_mem₁_provable h $ iff_not_mem₂_mem₁.mp hq₂;
  contradiction;

@[simp] lemma mem₁_verum : ⊤ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  apply by simpa using t.consistent (Γ := ∅) (Δ := {⊤}) (by simp) (by simpa);
  simp;

@[simp] lemma not_mem₁_falsum : ⊥ ∉ t.1.1 := by
  by_contra hC;
  have : 𝓢 ⊬ ⊥ 🡒 ⊥ := by simpa using t.consistent (Γ := {⊥}) (Δ := ∅) (by simpa) (by simp);
  apply this;
  simp;

@[simp] lemma mem₂_falsum : ⊥ ∈ t.1.2 := iff_not_mem₁_mem₂.mp not_mem₁_falsum

lemma mem₁_of_provable : 𝓢 ⊢ φ → φ ∈ t.1.1 := by
  intro h;
  exact mdp_mem₁_provable (C!_of_conseq! h) mem₁_verum;

lemma mdp_mem₁ [DecidableEq α] (h : φ 🡒 ψ ∈ t.1.1) (hp : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  apply t.consistent (Γ := {φ, φ 🡒 ψ}) (Δ := {ψ}) ?_ (by simpa);
  . apply CFConj_CDisj!_of_innerMDP (φ := φ) (ψ := ψ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    tauto;

lemma iff_mem₁_and [DecidableEq α] : φ ⋏ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∧ ψ ∈ t.1.1 := by
  constructor;
  . intro h; constructor <;> exact mdp_mem₁_provable (by simp) h
  . rintro ⟨hp, hq⟩;
    apply iff_not_mem₂_mem₁.mp;
    by_contra hC;
    apply t.consistent (Γ := {φ, ψ}) (Δ := {φ ⋏ ψ}) ?_ (by simp_all);
    . apply CFConj_CDisj!_of_K_intro (φ := φ) (ψ := ψ) <;> simp;
    . simp only [Finset.coe_insert, Finset.coe_singleton];
      apply Set.doubleton_subset.mpr;
      tauto;

lemma iff_mem₁_conj₂ [DecidableEq α] {Γ : List (Formula α)} : ⋀Γ ∈ t.1.1 ↔ ∀ φ ∈ Γ, φ ∈ t.1.1 := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ Γ_nil ih =>
    simp only [(List.conj₂_cons_nonempty Γ_nil), List.mem_cons];
    constructor;
    . rintro h φ (rfl | hp);
      . exact iff_mem₁_and.mp h |>.1;
      . exact ih.mp (iff_mem₁_and.mp h |>.2) _ hp;
    . intro h;
      apply iff_mem₁_and.mpr;
      simp_all;
  | _ => simp;

lemma iff_mem₁_fconj [DecidableEq α] {Γ : Finset (Formula α)} : Γ.conj ∈ t.1.1 ↔ ↑Γ ⊆ t.1.1 := by
  constructor;
  . intro h φ hφ;
    apply iff_mem₁_conj₂ (Γ := Γ.toList) (t := t) |>.mp;
    . apply mdp_mem₁_provable ?_ h; simp;
    . simpa;
  . intro h;
    apply mdp_mem₁_provable ?_ $ iff_mem₁_conj₂ (Γ := Γ.toList) (t := t) |>.mpr $ by
      intro φ hφ;
      apply h;
      simp_all;
    simp;

private lemma of_mem₁_or [DecidableEq α] : φ ⋎ ψ ∈ t.1.1 → (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC; push Not at hC;
  apply t.consistent (Γ := {φ ⋎ ψ}) (Δ := {φ, ψ}) (by simp_all) ?_;
  . apply CFConj_CDisj!_of_A (φ := φ) (ψ := ψ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    constructor;
    . exact iff_not_mem₁_mem₂.mp hC.1;
    . exact iff_not_mem₁_mem₂.mp hC.2;

private lemma of_mem₂_or : φ ⋎ ψ ∈ t.1.2 → φ ∈ t.1.2 ∧ ψ ∈ t.1.2 := by
  contrapose;
  suffices (φ ∉ t.1.2 ∨ ψ ∉ t.1.2) → φ ⋎ ψ ∉ t.1.2 by tauto;
  rintro (hφ | hψ);
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₁! $ iff_not_mem₂_mem₁.mp hφ;
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₂! $ iff_not_mem₂_mem₁.mp hψ;

lemma iff_mem₁_or [DecidableEq α] : φ ⋎ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∨ ψ ∈ t.1.1 := by
  constructor;
  . apply of_mem₁_or;
  . intro h;
    cases h with
    | inl h => exact mdp_mem₁_provable or₁! h;
    | inr h => exact mdp_mem₁_provable or₂! h;

lemma iff_mem₂_or [DecidableEq α] : φ ⋎ ψ ∈ t.1.2 ↔ φ ∈ t.1.2 ∧ ψ ∈ t.1.2 := by
  constructor;
  . apply of_mem₂_or;
  . contrapose;
    push Not;
    intro hφψ hφ;
    rcases iff_mem₁_or.mp $ iff_not_mem₂_mem₁.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₂_mem₁.mpr hφ; contradiction;
    . exact iff_not_mem₂_mem₁.mpr hψ;

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
  apply Iff.trans $ show Γ.disj ∈ t.1.2 ↔ ⋁Γ.toList ∈ t.1.2 by constructor <;> apply mdp_mem₂_provable $ by simp;
  apply Iff.trans iff_mem₂_disj;
  simp_all only [Finset.mem_toList];
  rfl;

lemma of_mem₁_imp [DecidableEq α] : φ 🡒 ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push Not at hC;
  exact hC.2 $ mdp_mem₁ h $ iff_not_mem₂_mem₁.mp hC.1

lemma of_mem₁_imp' [DecidableEq α] : φ 🡒 ψ ∈ t.1.1 → (φ ∈ t.1.1 → ψ ∈ t.1.1) := by
  intro h h₁;
  apply or_iff_not_imp_left.mp $ of_mem₁_imp h;
  apply iff_not_mem₂_mem₁.mpr h₁;

lemma of_mem₁_neg [DecidableEq α] (h : ∼φ ∈ t.1.1) : φ ∈ t.1.2 := by
  rcases of_mem₁_imp h with (hC | hC);
  . assumption;
  . exfalso;
    exact SaturatedConsistentTableau.not_mem₁_falsum hC;

lemma of_mem₁_neg' [DecidableEq α] (h : ∼φ ∈ t.1.1) : φ ∉ t.1.1 := by
  apply iff_not_mem₁_mem₂.mpr;
  apply of_mem₁_neg h;

omit [Entailment.Int 𝓢] in
private lemma of_mem₂_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  intro h;
  by_contra hC;
  replace hC := not_and_or.mp hC;
  rcases hC with (hφ | hψ);
  . have : φ ⋎ (φ 🡒 ψ) ∈ t.1.1 := iff_provable_mem₁.mp (A!_replace_right lem! CNC!) t;
    rcases iff_mem₁_or.mp this with (_ | _);
    . contradiction;
    . have := iff_not_mem₁_mem₂.mpr h;
      contradiction;
  . have : ψ 🡒 (φ 🡒 ψ) ∈ t.1.1 := iff_provable_mem₁.mp implyK! t;
    have : φ 🡒 ψ ∉ t.1.2 := iff_not_mem₂_mem₁.mpr $ mdp_mem₁ this (iff_not_mem₂_mem₁.mp hψ);
    contradiction;

omit [Entailment.Int 𝓢] in
lemma iff_mem₁_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.1 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_imp;
  . contrapose;
    push Not;
    intro hφψ;
    rcases of_mem₂_imp $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor;
    . exact iff_not_mem₂_mem₁.mpr hφ;
    . exact iff_not_mem₁_mem₂.mpr hψ;

omit [Entailment.Int 𝓢] in
lemma iff_mem₂_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ 🡒 ψ ∈ t.1.2 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_imp;
  . contrapose;
    push Not;
    intro hφψ hφ;
    rcases of_mem₁_imp $ iff_not_mem₂_mem₁.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₁_mem₂.mpr hφ; contradiction;
    . exact iff_not_mem₂_mem₁.mpr hψ;

lemma not_mem₁_neg_of_mem₁ [DecidableEq α] : φ ∈ t.1.1 → ∼φ ∉ t.1.1 := by
  intro hp;
  by_contra hnp;
  have := iff_mem₁_and.mpr ⟨hp, hnp⟩;
  have : ⊥ ∈ t.1.1 := mdp_mem₁_provable CKNO! this;
  have : ⊥ ∉ t.1.1 := not_mem₁_falsum
  contradiction;

lemma mem₂_neg_of_mem₁ [DecidableEq α] : φ ∈ t.1.1 → ∼φ ∈ t.1.2 := by
  intro h;
  exact iff_not_mem₁_mem₂ (φ := ∼φ) (t := t) |>.mp $ not_mem₁_neg_of_mem₁ h;

lemma mdp₁_mem [DecidableEq α] (hp : φ ∈ t.1.1) (h : φ 🡒 ψ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  apply t.consistent (Γ := {φ, φ 🡒 ψ}) (Δ := {ψ}) ?_ (by simpa);
  . apply CFConj_CDisj!_of_innerMDP (φ := φ) (ψ := ψ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    constructor <;> assumption;

end Saturated

end SaturatedConsistentTableau

end LO.Propositional
end

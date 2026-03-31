module

public import Foundation.Modal.Formula.Basic
public import Foundation.Modal.Entailment.K
public import Foundation.Vorspiel.Set.Basic

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Modal.Entailment

variable {α : Type*}
variable {S} [Entailment S (Formula α)]
variable {𝓢 : S}

def Tableau (α : Type u) := Set (Formula α) × Set (Formula α)

namespace Tableau

variable {t : Tableau α} {φ ψ : Formula α}

protected def Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : Finset (Formula α)}, (↑Γ ⊆ t.1) → (↑Δ ⊆ t.2) → 𝓢 ⊬ Γ.conj 🡒 Δ.disj

protected abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬t.Consistent 𝓢

protected structure Saturated (t : Tableau α) : Prop where
  implyK {φ ψ : Formula _} : φ 🡒 ψ ∈ t.1 → φ ∈ t.2 ∨ ψ ∈ t.1
  implyS {φ ψ : Formula _} : φ 🡒 ψ ∈ t.2 → φ ∈ t.1 ∧ ψ ∈ t.2

protected structure Disjoint (t : Tableau α) : Prop where
  union : Disjoint t.1 t.2
  no_bot : ⊥ ∉ t.1

protected def Maximal (t : Tableau α) := ∀ {φ}, φ ∈ t.1 ∨ φ ∈ t.2

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩
@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

section

variable [Entailment.Cl 𝓢]

lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : t.Disjoint := by
  constructor;
  . by_contra hC;
    obtain ⟨T, hT₁, hT₂, hT⟩ := by simpa [Disjoint] using hC;
    obtain ⟨φ, hφ⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hT;
    apply hCon (Γ := {φ}) (Δ := {φ})
      (by simp only [Finset.coe_singleton, Set.singleton_subset_iff]; apply hT₁; assumption)
      (by simp only [Finset.coe_singleton, Set.singleton_subset_iff]; apply hT₂; assumption);
    simp;
  . by_contra hC;
    apply hCon (Γ := {⊥}) (Δ := ∅) (by simpa) (by simp) $ by simp;

lemma mem₂_of_not_mem₁ (hMax : t.Maximal) : φ ∉ t.1 → φ ∈ t.2 := by
  intro h;
  cases hMax with
  | inl h' => contradiction;
  | inr _ => assumption;

lemma mem₁_of_not_mem₂ (hMax : t.Maximal) : φ ∉ t.2 → φ ∈ t.1 := by
  intro h;
  cases hMax with
  | inl _ => assumption;
  | inr h' => contradiction;

lemma iff_not_mem₁_mem₂ (hCon : t.Consistent 𝓢) (hMax : t.Maximal) : φ ∉ t.1 ↔ φ ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hMax;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon |>.1;

lemma iff_not_mem₂_mem₁ (hCon : t.Consistent 𝓢) (hMax : t.Maximal) : φ ∉ t.2 ↔ φ ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hMax;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon |>.1;

lemma maximal_duality
  {t₁ t₂ : Tableau α}
  (hCon₁ : t₁.Consistent 𝓢) (hCon₂ : t₂.Consistent 𝓢)
  (hMax₁ : t₁.Maximal) (hMax₂ : t₂.Maximal)
  : t₁.1 = t₂.1 ↔ t₁.2 = t₂.2 := by
  constructor;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply iff_not_mem₁_mem₂ hCon₂ hMax₂ |>.mp; rw [←h];
      apply iff_not_mem₁_mem₂ hCon₁ hMax₁ |>.mpr hp;
    . intro φ hp;
      apply iff_not_mem₁_mem₂ hCon₁ hMax₁ |>.mp; rw [h];
      apply iff_not_mem₁_mem₂ hCon₂ hMax₂ |>.mpr hp;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply iff_not_mem₂_mem₁ hCon₂ hMax₂ |>.mp; rw [←h];
      apply iff_not_mem₂_mem₁ hCon₁ hMax₁ |>.mpr hp;
    . intro φ hp;
      apply iff_not_mem₂_mem₁ hCon₁ hMax₁ |>.mp; rw [h];
      apply iff_not_mem₂_mem₁ hCon₂ hMax₂ |>.mpr hp;

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
    simp_all only [];
    apply h (Γ := Γ.erase φ) (Δ := Δ) (by simpa) hΔ;
    refine C!_trans ?_ hC;
    . exact C!_trans CKFConjinsertFConj! $ CFConj_FConj!_of_subset $ Finset.insert_erase_subset φ Γ

lemma iff_inconsistent_insert₁ : Tableau.Inconsistent 𝓢 ((insert φ T), U) ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ T) ∧ (↑Δ ⊆ U) ∧ 𝓢 ⊢ φ ⋏ Γ.conj 🡒 Δ.disj := by
  unfold Tableau.Inconsistent;
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₁.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₁.mp;

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

lemma iff_not_consistent_insert₂ : Tableau.Inconsistent 𝓢 (T, (insert φ U)) ↔ ∃ Γ Δ : Finset (Formula α), (↑Γ ⊆ T) ∧ (↑Δ ⊆ U) ∧ 𝓢 ⊢ Γ.conj 🡒 φ ⋎ Δ.disj := by
  unfold Tableau.Inconsistent;
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₂.mp;

lemma iff_consistent_empty_singleton₂ : Tableau.Consistent 𝓢 (∅, {φ}) ↔ 𝓢 ⊬ φ := by
  convert iff_consistent_insert₂ (𝓢 := 𝓢) (T := ∅) (U := ∅) (φ := φ);
  . simp;
  . constructor;
    . contrapose!;
      rintro ⟨Γ, Δ, hΓ, hΔ, h⟩;
      simp_all only [Set.subset_empty_iff, Finset.coe_eq_empty, Finset.conj_empty, Finset.disj_empty, not_not];
      simpa using A!_cases C!_id efq! ((by simpa using h) ⨀ verum!);
    . contrapose!;
      intro h;
      use ∅, ∅;
      refine ⟨by tauto, by tauto, ?_⟩;
      simp only [Finset.conj_empty, Finset.disj_empty, not_not];
      apply C!_of_conseq!;
      apply A!_intro_left (by simpa using h);

lemma iff_inconsistent_singleton₂ : Tableau.Inconsistent 𝓢 (∅, {φ}) ↔ 𝓢 ⊢ φ := by
  convert iff_consistent_empty_singleton₂ (𝓢 := 𝓢) (φ := φ) |>.not;
  tauto;

lemma either_expand_consistent_of_consistent (hCon : t.Consistent 𝓢) (φ : Formula α) : Tableau.Consistent 𝓢 ((insert φ t.1), t.2) ∨ Tableau.Consistent 𝓢 (t.1, (insert φ t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_inconsistent_insert₁.mp hC₁;
  replace h₁ := left_K!_symm h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;
  apply @hCon (Γ := Γ₁ ∪ Γ₂) (Δ := Δ₁ ∪ Δ₂) ?_ ?_;
  . exact C!_trans (C!_trans (by simp) (cut! h₁ h₂)) (by simp);
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;
  . simp only [Finset.coe_union, Set.union_subset_iff]; tauto;

lemma consistent_empty [H_consis : Entailment.Consistent 𝓢] : Tableau.Consistent 𝓢 ⟨∅, ∅⟩ := by
  intro Γ Δ hΓ hΔ;
  by_contra hC;
  obtain ⟨ψ, hψ⟩ := H_consis.exists_unprovable;
  apply hψ;
  simp only [Set.subset_empty_iff, Finset.coe_eq_empty] at hΓ hΔ;
  subst hΓ hΔ;
  simp only [Finset.conj_empty, Finset.disj_empty] at hC;
  exact of_O! (hC ⨀ C!_id);

end

section lindenbaum

open Classical
open Encodable

variable {t : Tableau α}

variable (𝓢 : S)

noncomputable def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent 𝓢 (insert φ t.1, t.2) then (insert φ t.1, t.2) else (t.1, insert φ t.2)

noncomputable def lindenbaum_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some φ => (lindenbaum_indexed t i).lindenbaum_next 𝓢 φ
    | none => lindenbaum_indexed t i
local notation:max t"[" i "]" => lindenbaum_indexed 𝓢 t i

def lindenbaum_max [Encodable α] (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_max 𝓢 t

variable {𝓢}

@[simp] lemma eq_lindenbaum_indexed_zero [Encodable α] {t : Tableau α} : t[0] = t := by simp [lindenbaum_indexed]

lemma consistent_lindenbaum_next [Entailment.Cl 𝓢] (consistent : t.Consistent 𝓢) (φ : Formula α) : (t.lindenbaum_next 𝓢 φ).Consistent 𝓢 := by
  unfold lindenbaum_next;
  split;
  . assumption;
  . rcases (either_expand_consistent_of_consistent consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma consistent_lindenbaum_indexed_succ [Entailment.Cl 𝓢] {i : ℕ} : t[i].Consistent 𝓢 → t[i + 1].Consistent 𝓢 := by
  simp only [lindenbaum_indexed];
  split;
  . intro h; apply consistent_lindenbaum_next h;
  . tauto;

lemma either_mem_lindenbaum_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp only [lindenbaum_indexed, encodek, lindenbaum_next];
  split <;> tauto;

lemma consistent_lindenbaum_indexed [Entailment.Cl 𝓢] (consistent : t.Consistent 𝓢) (i : ℕ) : t[i].Consistent 𝓢 := by
  induction i with
  | zero => simpa;
  | succ i ih => apply consistent_lindenbaum_indexed_succ; assumption;

variable {m n : ℕ}

lemma subset₁_lindenbaum_indexed_of_lt (h : m ≤ n) : t[m].1 ⊆ t[n].1 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_indexed, lindenbaum_next];
    split;
    . split <;> tauto;
    . tauto;

lemma subset₂_lindenbaum_indexed_of_lt (h : m ≤ n) : t[m].2 ⊆ t[n].2 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_indexed, lindenbaum_next];
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
    . apply subset₁_lindenbaum_indexed_of_lt (m := i);
      . omega;
      . simp_all;
    . intro ψ hq;
      exact subset₁_lindenbaum_indexed_of_lt (by simp) $ hm ψ hq;

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
    . apply subset₂_lindenbaum_indexed_of_lt (m := i);
      . omega;
      . simp_all
    . intro ψ hq;
      exact subset₂_lindenbaum_indexed_of_lt (by simp) $ hn ψ hq;

lemma exists_finset_lindenbaum_index₂ {Δ : Finset _} (hΓ : (SetLike.coe Δ) ⊆ ⋃ i, t[i].2) : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
  obtain ⟨m, hΔ⟩ := exists_list_lindenbaum_index₂ (Δ := Δ.toList) (𝓢 := 𝓢) (t := t) (by simpa);
  use m;
  intro φ hφ;
  apply hΔ;
  simpa;

lemma exists_consistent_saturated_tableau [Entailment.Cl 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (u.Consistent 𝓢) ∧ (u.Maximal) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?maximal⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case maximal =>
    intro φ;
    rcases either_mem_lindenbaum_indexed (𝓢 := 𝓢) t φ with (h | h);
    . left; simp only [lindenbaum_max, Set.mem_iUnion]; use (encode φ + 1);
    . right; simp only [lindenbaum_max, Set.mem_iUnion];  use (encode φ + 1);
  case consistent =>
    intro Γ Δ hΓ hΔ;
    simp_all only [lindenbaum_max];
    obtain ⟨m, hΓ⟩ := exists_finset_lindenbaum_index₁ hΓ;
    obtain ⟨n, hΔ⟩ := exists_finset_lindenbaum_index₂ hΔ;
    rcases (lt_trichotomy m n) with hm | hmn | hn;
    . exact consistent_lindenbaum_indexed hCon n (by intro φ hp; exact subset₁_lindenbaum_indexed_of_lt hm.le $ hΓ φ hp) hΔ;
    . subst hmn;
      exact consistent_lindenbaum_indexed hCon m hΓ hΔ;
    . exact consistent_lindenbaum_indexed hCon m hΓ (by intro φ hp; exact subset₂_lindenbaum_indexed_of_lt hn.le $ hΔ φ hp);

protected alias lindenbaum := exists_consistent_saturated_tableau

end lindenbaum

end Tableau

open Tableau

def MaximalConsistentTableau (𝓢 : S) := {t : Tableau α // t.Maximal ∧ t.Consistent 𝓢}

namespace MaximalConsistentTableau

variable {t t₁ t₂  : MaximalConsistentTableau 𝓢} {φ ψ : Formula α}

@[simp] lemma maximal (t : MaximalConsistentTableau 𝓢) : t.1.Maximal := t.2.1

@[simp] lemma consistent (t : MaximalConsistentTableau 𝓢) : t.1.Consistent 𝓢 := t.2.2

lemma lindenbaum {t₀ : Tableau α} [Entailment.Cl 𝓢] [Encodable α] (hCon : t₀.Consistent 𝓢) : ∃ (t : MaximalConsistentTableau 𝓢), t₀ ⊆ t.1 := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [Entailment.Consistent 𝓢] [Entailment.Cl 𝓢] [DecidableEq α] [Encodable α] : Nonempty (MaximalConsistentTableau 𝓢) := ⟨lindenbaum consistent_empty |>.choose⟩

variable {t t₁ t₂ : MaximalConsistentTableau 𝓢}

variable [Entailment.Cl 𝓢]

lemma disjoint : t.1.Disjoint := t.1.disjoint_of_consistent $ t.consistent

@[grind] lemma iff_not_mem₁_mem₂ : φ ∉ t.1.1 ↔ φ ∈ t.1.2 := Tableau.iff_not_mem₁_mem₂ t.consistent t.maximal

@[grind] lemma iff_not_mem₂_mem₁ : φ ∉ t.1.2 ↔ φ ∈ t.1.1 := Tableau.iff_not_mem₂_mem₁ t.consistent t.maximal

lemma neither : ¬(φ ∈ t.1.1 ∧ φ ∈ t.1.2) := by
  push_neg;
  intro h;
  exact iff_not_mem₂_mem₁.mpr h;

lemma maximal_duality: t₁.1.1 = t₂.1.1 ↔ t₁.1.2 = t₂.1.2 :=
  Tableau.maximal_duality t₁.consistent t₂.consistent t₁.maximal t₂.maximal

lemma equality_of₁ (e₁ : t₁.1.1 = t₂.1.1) : t₁ = t₂ := by
  calc
    t₁ = ⟨t₁.1, t₁.maximal, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.1, t₂.maximal, t₂.consistent⟩ := by simp [Tableau.equality_def.mpr ⟨e₁, (maximal_duality.mp e₁)⟩];

lemma equality_of₂ (e₂ : t₁.1.2 = t₂.1.2) : t₁ = t₂ := equality_of₁ $ maximal_duality.mpr e₂

lemma ne₁_of_ne : t₁ ≠ t₂ → t₁.1.1 ≠ t₂.1.1 := by
  contrapose!;
  exact equality_of₁;

lemma ne₂_of_ne : t₁ ≠ t₂ → t₁.1.2 ≠ t₂.1.2 := by
  contrapose!;
  exact equality_of₂;

lemma intro_equality (h₁ : ∀ {φ}, φ ∈ t₁.1.1 → φ ∈ t₂.1.1) (h₂ : ∀ {φ}, φ ∈ t₁.1.2 → φ ∈ t₂.1.2) : t₁ = t₂ := by
  apply equality_of₁;
  apply Set.eq_of_subset_of_subset;
  . intro φ hφ;
    exact h₁ hφ;
  . intro φ;
    contrapose;
    intro hφ;
    apply iff_not_mem₁_mem₂.mpr;
    exact h₂ $ iff_not_mem₁_mem₂.mp hφ;

section

variable [DecidableEq α] [Encodable α]

lemma iff_provable_include₁ : T *⊢[𝓢] φ ↔ ∀ t : MaximalConsistentTableau 𝓢, (T ⊆ t.1.1) → φ ∈ t.1.1 := by
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
      revert hC;
      contrapose!;
      intro h;
      replace h : T *⊢[𝓢] Δ.disj := Context.weakening! (by simpa using hΓ) $ FConj_DT.mp h;
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

lemma iff_provable_mem₁ : 𝓢 ⊢ φ ↔ ∀ t : MaximalConsistentTableau 𝓢, φ ∈ t.1.1 := by
  constructor;
  . intro h t;
    apply iff_provable_include₁ (T := ∅) |>.mp;
    . exact Context.of! h;
    . simp;
  . intro h;
    exact Context.emptyPrf! $ iff_provable_include₁.mpr $ by tauto;

end

section Saturated

variable [DecidableEq α] [Encodable α] {n : ℕ}

omit [Encodable α] in
lemma mdp_mem₁ (hφψ : φ 🡒 ψ ∈ t.1.1) (hφ : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hq₂;
  apply t.consistent (Γ := {φ, φ 🡒 ψ}) (Δ := {ψ}) ?_ ?_;
  . apply CFConj_CDisj!_of_innerMDP (φ := φ) (ψ := ψ) <;> simp;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    tauto;
  . simpa;

lemma mdp_mem₁_provable (hφψ : 𝓢 ⊢ φ 🡒 ψ) (hφ : φ ∈ t.1.1) : ψ ∈ t.1.1 := mdp_mem₁ (iff_provable_mem₁.mp hφψ t) hφ

lemma mdp_mem₂_provable (hφψ : 𝓢 ⊢ φ 🡒 ψ) : ψ ∈ t.1.2 → φ ∈ t.1.2 := by
  contrapose;
  intro hφ;
  apply iff_not_mem₂_mem₁.mpr;
  apply mdp_mem₁_provable hφψ;
  apply iff_not_mem₂_mem₁.mp hφ;

@[simp] lemma mem₁_verum : ⊤ ∈ t.1.1 := iff_provable_mem₁.mp verum! t

@[simp] lemma not_mem₂_verum : ⊤ ∉ t.1.2 := iff_not_mem₂_mem₁.mpr mem₁_verum

omit [Encodable α] [DecidableEq α] in
@[simp] lemma not_mem₁_falsum : ⊥ ∉ t.1.1 := disjoint.no_bot

omit [Encodable α] [DecidableEq α] in
@[simp] lemma mem₂_falsum : ⊥ ∈ t.1.2 := iff_not_mem₁_mem₂.mp not_mem₁_falsum

private lemma of_mem₁_and : φ ⋏ ψ ∈ t.1.1 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.1) := by
  intro h;
  constructor <;> exact mdp_mem₁_provable (by simp) h;

private lemma of_mem₂_and : φ ⋏ ψ ∈ t.1.2 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.2) := by
  contrapose;
  intro hφψ;
  apply iff_not_mem₂_mem₁.mpr;
  push_neg at hφψ;
  have hφ := iff_not_mem₂_mem₁.mp hφψ.1;
  have hψ := iff_not_mem₂_mem₁.mp hφψ.2;
  exact mdp_mem₁ (mdp_mem₁_provable and₃! hφ) hψ;

@[grind]
lemma iff_mem₁_and : φ ⋏ ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_and;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    rcases of_mem₂_and $ iff_not_mem₁_mem₂.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₁_mem₂.mpr hφ; contradiction;
    . exact iff_not_mem₁_mem₂.mpr hψ;

@[grind]
lemma iff_mem₂_and : φ ⋏ ψ ∈ t.1.2 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_and;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₁_and $ iff_not_mem₂_mem₁.mp hφψ with ⟨hφ, hψ⟩;
    constructor <;> { apply iff_not_mem₂_mem₁.mpr; assumption; };

lemma iff_mem₁_conj₂ {Γ : List (Formula α)} : ⋀Γ ∈ t.1.1 ↔ ∀ φ ∈ Γ, φ ∈ t.1.1 := by
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

lemma iff_mem₁_fconj {Γ : Finset (Formula α)} : Γ.conj ∈ t.1.1 ↔ ↑Γ ⊆ t.1.1 := by
  constructor;
  . intro h φ hφ;
    apply iff_mem₁_conj₂ (Γ := Γ.toList) (t := t) |>.mp;
    . apply mdp_mem₁_provable ?_ h; simp;
    . simpa;
  . intro h;
    apply mdp_mem₁_provable ?_ $ iff_mem₁_conj₂ (Γ := Γ.toList) (t := t) |>.mpr $ by
      intro φ hφ;
      apply h;
      simpa using hφ;
    simp;

lemma iff_mem₂_conj₂ {Γ : List _} : ⋀Γ ∈ t.1.2 ↔ (∃ φ ∈ Γ, φ ∈ t.1.2) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    rw [List.conj₂_cons_nonempty hΓ];
    constructor;
    . intro h;
      rcases iff_mem₂_and.mp h with (hφ | hΓ);
      . exact ⟨φ, by tauto, hφ⟩;
      . obtain ⟨ψ, hψ₁, hψ₂⟩ := ih.mp hΓ;
        exact ⟨ψ, by tauto, hψ₂⟩;
    . rintro ⟨ψ, (hψ₁ | hψ₁), hψ₂⟩;
      . apply iff_mem₂_and.mpr;
        left;
        assumption;
      . apply iff_mem₂_and.mpr;
        right;
        apply ih.mpr;
        exact ⟨ψ, by simpa, hψ₂⟩;
  | _ => simp;

lemma iff_mem₂_fconj {Γ : Finset (Formula α)} : Γ.conj ∈ t.1.2 ↔ (∃ φ ∈ Γ, φ ∈ t.1.2)  := by
  constructor;
  . intro h;
    obtain ⟨φ, hφ₁, hφ₂⟩ := iff_mem₂_conj₂ (Γ := Γ.toList) (t := t) |>.mp $ by
      apply mdp_mem₂_provable (ψ := Γ.conj);
      . simp;
      . assumption;
    use φ;
    constructor;
    . simpa using hφ₁;
    . simpa;
  . rintro ⟨ψ, hψ₁, hψ₂⟩;
    apply iff_mem₂_conj₂.mpr;
    use ψ;
    constructor <;> simpa;

omit [Encodable α] in
private lemma of_mem₁_or : φ ⋎ ψ ∈ t.1.1 → (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra! hC;
  apply t.consistent (Γ := {φ ⋎ ψ}) (Δ := {φ, ψ}) ?_ ?_;
  . apply CFConj_CDisj!_of_A (φ := φ) (ψ := ψ) <;> simp;
  . simpa;
  . simp only [Finset.coe_insert, Finset.coe_singleton];
    apply Set.doubleton_subset.mpr;
    constructor;
    . exact iff_not_mem₁_mem₂.mp hC.1;
    . exact iff_not_mem₁_mem₂.mp hC.2;

private lemma of_mem₂_or : φ ⋎ ψ ∈ t.1.2 → (φ ∈ t.1.2 ∧ ψ ∈ t.1.2) := by
  contrapose;
  suffices (φ ∉ t.1.2 ∨ ψ ∉ t.1.2) → φ ⋎ ψ ∉ t.1.2 by tauto;
  rintro (hφ | hψ);
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₁! $ iff_not_mem₂_mem₁.mp hφ;
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₂! $ iff_not_mem₂_mem₁.mp hψ;

@[grind]
lemma iff_mem₁_or : φ ⋎ ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_or;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₂_or $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor <;> { apply iff_not_mem₁_mem₂.mpr; assumption; };

@[grind]
lemma iff_mem₂_or : φ ⋎ ψ ∈ t.1.2 ↔ (φ ∈ t.1.2 ∧ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_or;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    rcases of_mem₁_or $ iff_not_mem₂_mem₁.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₂_mem₁.mpr hφ; contradiction;
    . exact iff_not_mem₂_mem₁.mpr hψ;

lemma iff_mem₁_disj  {Γ : List _} : ⋁Γ ∈ t.1.1 ↔ (∃ φ ∈ Γ, φ ∈ t.1.1) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    rw [List.disj₂_cons_nonempty hΓ];
    constructor;
    . intro h;
      rcases iff_mem₁_or.mp h with (hφ | hΓ);
      . exact ⟨φ, by tauto, hφ⟩;
      . obtain ⟨ψ, hψ₁, hψ₂⟩ := ih.mp hΓ;
        exact ⟨ψ, by tauto, hψ₂⟩;
    . rintro ⟨ψ, (hψ₁ | hψ₁), hψ₂⟩;
      . apply iff_mem₁_or.mpr;
        left;
        assumption;
      . apply iff_mem₁_or.mpr;
        right;
        apply ih.mpr;
        exact ⟨ψ, by simpa, hψ₂⟩;
  | _ => simp;

lemma iff_mem₂_disj {Γ : List _} : ⋁Γ ∈ t.1.2 ↔ (∀ φ ∈ Γ, φ ∈ t.1.2) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    rw [List.disj₂_cons_nonempty hΓ];
    constructor;
    . intro h;
      rcases iff_mem₂_or.mp h with ⟨hφ, hΓ⟩;
      rintro ψ (hψ | hΓ);
      . assumption;
      . apply ih.mp hΓ;
        assumption;
    . intro h;
      apply iff_mem₂_or.mpr;
      constructor;
      . apply h; tauto;
      . apply ih.mpr;
        intro ψ hψ;
        apply h;
        tauto;
  | _ => simp;

lemma iff_mem₂_fdisj {Γ : Finset _} : Γ.disj ∈ t.1.2 ↔ (↑Γ ⊆ t.1.2) := by
  constructor;
  . intro h φ hφ;
    apply iff_mem₂_disj (Γ := Γ.toList) (t := t) |>.mp;
    . apply mdp_mem₂_provable ?_ h; simp;
    . simpa;
  . intro h;
    apply mdp_mem₂_provable ?_ $ iff_mem₂_disj (Γ := Γ.toList) (t := t) |>.mpr $ by
      intro φ hφ;
      apply h;
      simpa using hφ;
    simp;

omit [Encodable α] in
private lemma of_mem₁_imp : φ 🡒 ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push_neg at hC;
  exact hC.2 $ mdp_mem₁ h $ iff_not_mem₂_mem₁.mp hC.1

private lemma of_mem₂_imp : φ 🡒 ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  intro h;
  by_contra hC;
  replace hC := not_and_or.mp hC;
  rcases hC with (hφ | hψ);
  . have : φ ⋎ (φ 🡒 ψ) ∈ t.1.1 := iff_provable_mem₁.mp (A!_replace_right lem! CNC!) t;
    rcases of_mem₁_or this with (_ | _);
    . contradiction;
    . have := iff_not_mem₁_mem₂.mpr h;
      contradiction;
  . have : ψ 🡒 (φ 🡒 ψ) ∈ t.1.1 := iff_provable_mem₁.mp implyK! t;
    have : φ 🡒 ψ ∉ t.1.2 := iff_not_mem₂_mem₁.mpr $ mdp_mem₁ this (iff_not_mem₂_mem₁.mp hψ);
    contradiction;

@[grind]
lemma iff_mem₁_imp : φ 🡒 ψ ∈ t.1.1 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_imp;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₂_imp $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor;
    . exact iff_not_mem₂_mem₁.mpr hφ;
    . exact iff_not_mem₁_mem₂.mpr hψ;

@[grind]
lemma iff_mem₁_imp' : φ 🡒 ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 → ψ ∈ t.1.1) := by
  simp [iff_mem₁_imp, or_iff_not_imp_left, iff_not_mem₂_mem₁];

@[grind]
lemma iff_mem₂_imp : φ 🡒 ψ ∈ t.1.2 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_imp;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    rcases of_mem₁_imp $ iff_not_mem₂_mem₁.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₁_mem₂.mpr hφ; contradiction;
    . exact iff_not_mem₂_mem₁.mpr hψ;

omit [Encodable α] in
private lemma of_mem₁_neg : ∼φ ∈ t.1.1 → (φ ∈ t.1.2) := by
  intro h;
  rcases of_mem₁_imp h with (hφ | hb);
  . assumption;
  . exfalso;
    exact not_mem₁_falsum hb;

private lemma of_mem₂_neg : ∼φ ∈ t.1.2 → (φ ∈ t.1.1) := by
  intro h;
  rcases of_mem₂_imp h with ⟨hφ, hb⟩;
  exact hφ;

@[grind]
lemma iff_mem₁_neg : ∼φ ∈ t.1.1 ↔ φ ∈ t.1.2 := by
  constructor;
  . apply of_mem₁_neg;
  . contrapose;
    intro h;
    exact iff_not_mem₂_mem₁.mpr $ of_mem₂_neg $ iff_not_mem₁_mem₂.mp h

@[grind]
lemma iff_mem₁_neg' : ∼φ ∈ t.1.1 ↔ φ ∉ t.1.1 := Iff.trans iff_mem₁_neg $ Iff.symm iff_not_mem₁_mem₂

@[grind]
lemma iff_mem₂_neg : ∼φ ∈ t.1.2 ↔ φ ∈ t.1.1 := by
  constructor;
  . apply of_mem₂_neg;
  . contrapose;
    intro h;
    exact iff_not_mem₁_mem₂.mpr $ of_mem₁_neg $ iff_not_mem₂_mem₁.mp h

@[grind]
lemma iff_mem₂_neg' : ∼φ ∈ t.1.2 ↔ φ ∉ t.1.2 := Iff.trans iff_mem₂_neg $ Iff.symm iff_not_mem₂_mem₁

section

variable [Entailment.K 𝓢]

omit [Entailment.Cl 𝓢] [Entailment.K 𝓢] [DecidableEq α] [Encodable α] in
private lemma of_mem₁_boxItr : (□^[n]φ ∈ t.1.1) → (∀ {t' : MaximalConsistentTableau 𝓢}, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) → (φ ∈ t'.1.1)) := by
  intro h t' ht';
  apply ht';
  grind;

private lemma of_mem₂_boxItr : (□^[n]φ ∈ t.1.2) → (∃ t' : MaximalConsistentTableau 𝓢, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := by
  intro h;
  obtain ⟨t', ht'⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨(□⁻¹^[n]'t.1.1), {φ}⟩) $ by
    intro Γ Δ hΓ hΔ;
    by_contra! hC;
    apply t.consistent (Γ := (□^[n]'Γ)) (Δ := {□^[n]φ}) ?_ ?_;
    . simp only [Finset.disj_singleton];
      exact C!_trans collect_boxItr_fconj! $ imply_boxItr_distribute'! $ C!_trans hC (left_Fdisj!_intro' hΔ);
    . rintro ψ hψ;
      obtain ⟨ξ, hξ, rfl⟩ := Finset.LO.exists_of_mem_boxItr hψ;
      simp at hΓ;
      simpa using hΓ $ by simpa;
    . simpa;
  use t';
  constructor;
  . exact ht'.1;
  . apply ht'.2;
    tauto;

lemma iff_mem₁_boxItr : (□^[n]φ ∈ t.1.1) ↔ (∀ {t' : MaximalConsistentTableau 𝓢}, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) → (φ ∈ t'.1.1)) := by
  constructor;
  . apply of_mem₁_boxItr;
  . contrapose;
    push_neg;
    intro hφ;
    obtain ⟨t', ht'₁, ht'₂⟩ := of_mem₂_boxItr $ iff_not_mem₁_mem₂.mp hφ;
    use t';
    constructor;
    . exact ht'₁;
    . exact iff_not_mem₁_mem₂.mpr ht'₂;

lemma iff_mem₁_box : (□φ ∈ t.1.1) ↔ (∀ {t' : MaximalConsistentTableau 𝓢}, ((□⁻¹'t.1.1) ⊆ t'.1.1) → (φ ∈ t'.1.1)) := iff_mem₁_boxItr (n := 1)

lemma iff_mem₂_boxItr : (□^[n]φ ∈ t.1.2) ↔ (∃ t' : MaximalConsistentTableau 𝓢, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := by
  constructor;
  . apply of_mem₂_boxItr;
  . contrapose;
    push_neg;
    intro hφ t' ht';
    exact iff_not_mem₂_mem₁.mpr $ of_mem₁_boxItr (iff_not_mem₂_mem₁.mp hφ) ht';

lemma iff_mem₂_box : (□φ ∈ t.1.2) ↔ (∃ t' : MaximalConsistentTableau 𝓢, ((□⁻¹'t.1.1) ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := iff_mem₂_boxItr (n := 1)

lemma iff_mem₁_diaItr : (◇^[n]φ ∈ t.1.1) ↔ (∃ t' : MaximalConsistentTableau 𝓢, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) ∧ (φ ∈ t'.1.1)) := by
  suffices ◇^[n]φ ∈ t.1.1 ↔ ∃ t' : MaximalConsistentTableau 𝓢, (□⁻¹^[n]'t.1.1) ⊆ t'.1.1 ∧ ∼φ ∈ t'.1.2 by simpa [iff_mem₂_neg];
  apply Iff.trans ?_ iff_mem₂_boxItr;
  rw [←iff_mem₁_neg];
  constructor;
  . apply mdp_mem₁_provable; simp;
  . apply mdp_mem₁_provable; simp;

lemma iff_mem₁_dia : (◇φ ∈ t.1.1) ↔ (∃ t' : MaximalConsistentTableau 𝓢, ((□⁻¹'t.1.1) ⊆ t'.1.1) ∧ (φ ∈ t'.1.1)) := iff_mem₁_diaItr (n := 1)

lemma iff_mem₂_diaItr : (◇^[n]φ ∈ t.1.2) ↔ (∀ t' : MaximalConsistentTableau 𝓢, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) → (φ ∈ t'.1.2)) := by
  suffices ◇^[n]φ ∈ t.1.2 ↔ (∀ t' : MaximalConsistentTableau 𝓢, ((□⁻¹^[n]'t.1.1) ⊆ t'.1.1) → (∼φ ∈ t'.1.1)) by simpa [iff_mem₁_neg]
  apply Iff.trans ?_ iff_mem₁_boxItr;
  rw [←iff_mem₁_neg];
  constructor;
  . apply mdp_mem₁_provable;
    apply CN!_of_CN!_left;
    simp;
  . apply mdp_mem₁_provable;
    apply CN!_of_CN!_right;
    simp;

lemma iff_mem₂_dia : (◇φ ∈ t.1.2) ↔ (∀ t' : MaximalConsistentTableau 𝓢, ((□⁻¹'t.1.1) ⊆ t'.1.1) → (φ ∈ t'.1.2)) := iff_mem₂_diaItr (n := 1)

end

end Saturated

section

lemma _root_.Set.exists_of_ne {s t : Set α} (h : s ≠ t) : ∃ x, ((x ∈ s ∧ x ∉ t) ∨ (x ∉ s ∧ x ∈ t)) := by
  revert h;
  contrapose!;
  intro h;
  ext x;
  rcases h x with ⟨h₁, h₂⟩;
  constructor;
  . assumption;
  . tauto;

variable [DecidableEq α] [Encodable α]

lemma exists₁₂_of_ne {y z : MaximalConsistentTableau 𝓢} (eyz : y ≠ z) : ∃ φ₂, φ₂ ∈ y.1.1 ∧ φ₂ ∈ z.1.2 := by
  obtain ⟨ξ, hξ⟩ := Set.exists_of_ne $ ne₁_of_ne eyz;
  rcases hξ with (⟨hξy₁, hξy₂⟩ | ⟨hξz₁, hξy₂⟩);
  . use ξ;
    constructor;
    . exact hξy₁;
    . exact iff_not_mem₁_mem₂.mp hξy₂;
  . use ∼ξ;
    constructor;
    . apply iff_mem₁_neg.mpr;
      exact iff_not_mem₁_mem₂.mp hξz₁;
    . apply iff_mem₂_neg.mpr;
      exact hξy₂;

lemma exists₂₁_of_ne {y z : MaximalConsistentTableau 𝓢} (eyz : y ≠ z) : ∃ φ₁, φ₁ ∈ y.1.2 ∧ φ₁ ∈ z.1.1 := by
  obtain ⟨ξ, hξ⟩ := Set.exists_of_ne $ ne₂_of_ne eyz;
  rcases hξ with (⟨hξy₁, hξy₂⟩ | ⟨hξz₁, hξy₂⟩);
  . use ξ;
    constructor;
    . exact hξy₁;
    . exact iff_not_mem₂_mem₁.mp hξy₂;
  . use ∼ξ;
    constructor;
    . apply iff_mem₂_neg.mpr;
      exact iff_not_mem₂_mem₁.mp hξz₁;
    . apply iff_mem₁_neg.mpr;
      exact hξy₂;

end

end MaximalConsistentTableau

end LO.Modal
end

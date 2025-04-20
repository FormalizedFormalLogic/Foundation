import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K

namespace LO.Modal

open Entailment
variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}


def Tableau (α : Type u) := Set (Formula α) × Set (Formula α)

namespace Tableau

variable {t : Tableau α} {φ ψ : Formula α}

protected def Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ t.1) → (∀ φ ∈ Δ, φ ∈ t.2) → 𝓢 ⊬ ⋀Γ ➝ ⋁Δ

protected abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬t.Consistent 𝓢

protected structure Saturated (t : Tableau α) : Prop where
  imply₁ {φ ψ} : φ ➝ ψ ∈ t.1 → φ ∈ t.2 ∨ ψ ∈ t.1
  imply₂ {φ ψ} : φ ➝ ψ ∈ t.2 → φ ∈ t.1 ∧ ψ ∈ t.2

protected structure Disjoint (t : Tableau α) : Prop where
  union : Disjoint t.1 t.2
  no_bot : ⊥ ∉ t.1

protected def Maximal (t : Tableau α) := ∀ {φ}, φ ∈ t.1 ∨ φ ∈ t.2

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩
@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl


section

variable [Entailment.Modal.K 𝓢]

lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : t.Disjoint := by
  constructor;
  . by_contra hC;
    obtain ⟨T, hT₁, hT₂, hT⟩ := by simpa [Disjoint] using hC;
    obtain ⟨φ, hφ⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hT;
    unfold Tableau.Consistent at hCon;
    have : 𝓢 ⊬ ⋀[φ] ➝ ⋁[φ] := hCon
      (by simp_all; apply hT₁; assumption)
      (by simp_all; apply hT₂; assumption);
    have : 𝓢 ⊢! ⋀[φ] ➝ ⋁[φ] := by simp;
    contradiction;
  . by_contra hC;
    exact hCon (Γ := [⊥]) (Δ := []) (by simpa) (by simp) $ by simp;

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
  : Tableau.Consistent 𝓢 ((insert φ T), U) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ T) → (∀ φ ∈ Δ, φ ∈ U) → 𝓢 ⊬ φ ⋏ ⋀Γ ➝ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : 𝓢 ⊬ ⋀(φ :: Γ) ➝ ⋁Δ := h (by simp; intro ψ hψ; right; exact hΓ ψ hψ;) hΔ;
    have : 𝓢 ⊢! ⋀(φ :: Γ) ➝ ⋁Δ := CConj₂!_iff_CKConj₂!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all only [Set.mem_insert_iff];
    have : 𝓢 ⊬ φ ⋏ ⋀(Γ.remove φ) ➝ ⋁Δ := h (by
      intro ψ hq;
      have := by simpa using hΓ ψ $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    ) hΔ;
    by_contra hC;
    have : 𝓢 ⊢! φ ⋏ ⋀(Γ.remove φ) ➝ ⋁Δ := C!_trans CKK! $ CKConj₂Remove!_of_CConj₂! (φ := φ) hC;
    contradiction;

lemma iff_inconsistent_insert₁ : Tableau.Inconsistent 𝓢 ((insert φ T), U) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ 𝓢 ⊢! φ ⋏ ⋀Γ ➝ ⋁Δ := by
  unfold Tableau.Inconsistent;
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₁.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₁.mp;

lemma iff_consistent_insert₂ : Tableau.Consistent 𝓢 (T, (insert φ U)) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ T) → (∀ φ ∈ Δ, φ ∈ U) → 𝓢 ⊬ ⋀Γ ➝ φ ⋎ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : 𝓢 ⊬ ⋀Γ ➝ ⋁(φ :: Δ) := h hΓ (by simp; intro ψ hq; right; exact hΔ ψ hq);
    have : 𝓢 ⊢! ⋀Γ ➝ ⋁(φ :: Δ) := CDisj₂!_iff_CADisj₂!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all;
    have : 𝓢 ⊬ ⋀Γ ➝ φ ⋎ ⋁(Δ.remove φ) := h hΓ (by
      intro ψ hq;
      have := by simpa using hΔ ψ $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have : 𝓢 ⊢! ⋀Γ ➝ φ ⋎ ⋁(Δ.remove φ) := C!_trans hC $ CDisj₂ADisj₂Remove!;
    contradiction;

lemma iff_not_consistent_insert₂ : Tableau.Inconsistent 𝓢 (T, (insert φ U)) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ 𝓢 ⊢! ⋀Γ ➝ φ ⋎ ⋁Δ := by
  unfold Tableau.Inconsistent;
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₂.mp;

lemma iff_consistent_empty_singleton₂ : Tableau.Consistent 𝓢 (∅, {φ}) ↔ 𝓢 ⊬ φ := by
  convert iff_consistent_insert₂ (𝓢 := 𝓢) (T := ∅) (U := ∅) (φ := φ);
  . simp;
  . constructor;
    . contrapose;
      push_neg;
      rintro ⟨Γ, Δ, hΓ, hΔ, h⟩;
      have : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
      have : Δ = [] := List.eq_nil_iff_forall_not_mem.mpr hΔ;
      subst Γ Δ;
      simpa using A!_cases C!_id efq! ((by simpa using h) ⨀ verum!);
    . contrapose;
      push_neg;
      intro h;
      use [], [];
      refine ⟨by tauto, by tauto, ?_⟩;
      simp only [List.conj₂_nil, List.disj₂_nil, not_not];
      apply C!_of_conseq!;
      apply A!_intro_left (by simpa using h);

lemma iff_inconsistent_singleton₂ : Tableau.Inconsistent 𝓢 (∅, {φ}) ↔ 𝓢 ⊢! φ := by
  convert iff_consistent_empty_singleton₂ (𝓢 := 𝓢) (φ := φ) |>.not;
  tauto;

lemma either_expand_consistent_of_consistent (hCon : t.Consistent 𝓢) (φ : Formula α) : Tableau.Consistent 𝓢 ((insert φ t.1), t.2) ∨ Tableau.Consistent 𝓢 (t.1, (insert φ t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_inconsistent_insert₁.mp hC₁;
  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;

  replace h₁ := left_K!_symm h₁;

  have : 𝓢 ⊢! ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := C!_trans (K!_left EConj₂AppendKConj₂Conj₂!) $ C!_trans (cut! h₁ h₂) (K!_right EDisj₂AppendADisj₂Disj₂!);
  have : 𝓢 ⊬ ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := hCon
    (by simp; rintro ψ (hq₁ | hq₂); exact hΓ₁ ψ hq₁; exact hΓ₂ ψ hq₂)
    (by simp; rintro ψ (hq₁ | hq₂); exact hΔ₁ ψ hq₁; exact hΔ₂ ψ hq₂);
  contradiction;

lemma consistent_empty [H_consis : Entailment.Consistent 𝓢] : Tableau.Consistent 𝓢 ⟨∅, ∅⟩ := by
  intro Γ Δ hΓ hΔ;
  replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  replace hΔ : Δ = [] := List.eq_nil_iff_forall_not_mem.mpr hΔ;
  subst hΓ hΔ;
  by_contra hC;
  simp only [List.conj₂_nil, List.disj₂_nil] at hC;
  obtain ⟨ψ, hψ⟩ := H_consis.exists_unprovable;
  have : 𝓢 ⊢! ψ := of_O! (hC ⨀ C!_id);
  contradiction;

end


section lindenbaum

open Classical
open Encodable

variable {t : Tableau α}

variable (𝓢 : S)

def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent 𝓢 (insert φ t.1, t.2) then (insert φ t.1, t.2) else (t.1, insert φ t.2)

def lindenbaum_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
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

lemma consistent_lindenbaum_next [Entailment.Modal.K 𝓢] (consistent : t.Consistent 𝓢) (φ : Formula α) : (t.lindenbaum_next 𝓢 φ).Consistent 𝓢 := by
  unfold lindenbaum_next;
  split;
  . assumption;
  . rcases (either_expand_consistent_of_consistent consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma consistent_lindenbaum_indexed_succ [Entailment.Modal.K 𝓢] {i : ℕ} : t[i].Consistent 𝓢 → t[i + 1].Consistent 𝓢 := by
  simp only [lindenbaum_indexed];
  split;
  . intro h; apply consistent_lindenbaum_next h;
  . tauto;

lemma either_mem_lindenbaum_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp only [lindenbaum_indexed, encodek, lindenbaum_next];
  split <;> tauto;

lemma consistent_lindenbaum_indexed [Entailment.Modal.K 𝓢] (consistent : t.Consistent 𝓢) (i : ℕ) : t[i].Consistent 𝓢 := by
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

lemma exists_consistent_saturated_tableau [Entailment.Modal.K 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (u.Consistent 𝓢) ∧ (u.Maximal) := by
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
    simp_all only [lindenbaum_max, Set.mem_iUnion];
    obtain ⟨m, hΓ⟩ : ∃ m, ∀ φ ∈ Γ, φ ∈ t[m].1 := by
      induction Γ with
      | nil => simp;
      | cons φ Γ ih =>
        simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp];
        obtain ⟨i, hi⟩ := hΓ.1;
        obtain ⟨m, hm⟩ := ih;
        use (i + m);
        constructor;
        . exact subset₁_lindenbaum_indexed_of_lt (by omega) hi;
        . intro ψ hq;
          exact subset₁_lindenbaum_indexed_of_lt (by omega) $ hm ψ hq;
    obtain ⟨n, hΔ⟩ : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
      induction Δ with
      | nil => simp;
      | cons φ Δ ih =>
        simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp];
        obtain ⟨i, hi⟩ := hΔ.1;
        obtain ⟨n, hn⟩ := ih;
        use (i + n);
        constructor;
        . exact subset₂_lindenbaum_indexed_of_lt (by omega) hi;
        . intro ψ hq;
          exact subset₂_lindenbaum_indexed_of_lt (by omega) $ hn ψ hq;
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

lemma lindenbaum {t₀ : Tableau α} [Entailment.Modal.K 𝓢] [Encodable α] (hCon : t₀.Consistent 𝓢) : ∃ (t : MaximalConsistentTableau 𝓢), t₀ ⊆ t.1 := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [Entailment.Consistent 𝓢] [Entailment.Modal.K 𝓢] [DecidableEq α] [Encodable α] : Nonempty (MaximalConsistentTableau 𝓢) := ⟨lindenbaum consistent_empty |>.choose⟩

variable {t t₁ t₂ : MaximalConsistentTableau 𝓢}

variable [Entailment.Modal.K 𝓢]

lemma disjoint : t.1.Disjoint := t.1.disjoint_of_consistent $ t.consistent

lemma iff_not_mem₁_mem₂ : φ ∉ t.1.1 ↔ φ ∈ t.1.2 := Tableau.iff_not_mem₁_mem₂ t.consistent t.maximal

lemma iff_not_mem₂_mem₁ : φ ∉ t.1.2 ↔ φ ∈ t.1.1 := Tableau.iff_not_mem₂_mem₁ t.consistent t.maximal

lemma neither : ¬(φ ∈ t.1.1 ∧ φ ∈ t.1.2) := by
  push_neg;
  intro h;
  exact iff_not_mem₂_mem₁.mpr h;

lemma maximal_duality: t₁.1.1 = t₂.1.1 ↔ t₁.1.2 = t₂.1.2 :=
  Tableau.maximal_duality t₁.consistent t₂.consistent t₁.maximal t₂.maximal

lemma equality_of₁ (e₁ : t₁.1.1 = t₂.1.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (maximal_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.1, t₁.maximal, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.1, t₂.maximal, t₂.consistent⟩ := by simp [e];
    _  = t₂                                := by rfl;

lemma equality_of₂ (e₂ : t₁.1.2 = t₂.1.2) : t₁ = t₂ := equality_of₁ $ maximal_duality.mpr e₂

lemma ne₁_of_ne : t₁ ≠ t₂ → t₁.1.1 ≠ t₂.1.1 := by
  contrapose;
  push_neg;
  exact equality_of₁;

lemma ne₂_of_ne : t₁ ≠ t₂ → t₁.1.2 ≠ t₂.1.2 := by
  contrapose;
  push_neg;
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

lemma iff_provable_include₁ : T *⊢[𝓢]! φ ↔ ∀ t : MaximalConsistentTableau 𝓢, (T ⊆ t.1.1) → φ ∈ t.1.1 := by
  constructor;
  . intro h t hT;
    by_contra hφ;
    replace hφ := iff_not_mem₁_mem₂.mp hφ;
    obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    have := t.consistent (Γ := Γ) (Δ := [φ]) ?_ ?_;
    contradiction;
    . tauto_set;
    . simpa;
  . intro h;
    by_contra hC;
    obtain ⟨t, ht⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨T, {φ}⟩) $ by
      intro Γ Δ hΓ hΔ;
      replace hΔ := by simpa using hΔ;
      replace hC := Context.provable_iff.not.mp hC;
      push_neg at hC;
      have := hC Γ (by aesop);
      suffices 𝓢 ⊬ ⋀Γ ➝ φ by
        by_contra hC;
        have : 𝓢 ⊢! ⋀Γ ➝ φ := C!_trans hC $ left_Disj₂!_intro' $ by simpa
        contradiction;
      exact this;
    have := iff_not_mem₂_mem₁.mpr $ h t ht.1;
    have := ht.2;
    tauto_set;

lemma iff_provable_mem₁ : 𝓢 ⊢! φ ↔ ∀ t : MaximalConsistentTableau 𝓢, φ ∈ t.1.1 := by
  constructor;
  . intro h t;
    apply iff_provable_include₁ (T := ∅) |>.mp;
    . exact Context.of! h;
    . simp;
  . intro h;
    exact Context.emptyPrf! $ iff_provable_include₁.mpr $ by tauto;

end


section Saturated

variable [DecidableEq α] [Encodable α]

omit [Encodable α] in
lemma mdp_mem₁ (hφψ : φ ➝ ψ ∈ t.1.1) (hφ : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hq₂;
  have : 𝓢 ⊬ ⋀[φ, φ ➝ ψ] ➝ ⋁[ψ] := t.consistent (Γ := [φ, φ ➝ ψ]) (Δ := [ψ]) (by simp_all) (by simp_all);
  have : 𝓢 ⊢! ⋀[φ, φ ➝ ψ] ➝ ⋁[ψ] := inner_mdp!
  contradiction;

lemma mdp_mem₁_provable (hφψ : 𝓢 ⊢! φ ➝ ψ) (hφ : φ ∈ t.1.1) : ψ ∈ t.1.1 := mdp_mem₁ (iff_provable_mem₁.mp hφψ t) hφ

lemma mdp_mem₂_provable (hφψ : 𝓢 ⊢! φ ➝ ψ) : ψ ∈ t.1.2 → φ ∈ t.1.2 := by
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

lemma iff_mem₁_and : φ ⋏ ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_and;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    rcases of_mem₂_and $ iff_not_mem₁_mem₂.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₁_mem₂.mpr hφ; contradiction;
    . exact iff_not_mem₁_mem₂.mpr hψ;

lemma iff_mem₂_and : φ ⋏ ψ ∈ t.1.2 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_and;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₁_and $ iff_not_mem₂_mem₁.mp hφψ with ⟨hφ, hψ⟩;
    constructor <;> { apply iff_not_mem₂_mem₁.mpr; assumption; };

lemma iff_mem₁_conj {Γ : List _} : ⋀Γ ∈ t.1.1 ↔ (∀ φ ∈ Γ, φ ∈ t.1.1) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ hΓ ih =>
    rw [List.conj₂_cons_nonempty hΓ]
    constructor;
    . intro h;
      rcases iff_mem₁_and.mp h with ⟨hφ, hΓ⟩;
      rintro ψ (hψ | hψ);
      . assumption;
      . apply ih.mp hΓ ψ;
        assumption;
    . intro h;
      apply iff_mem₁_and.mpr;
      constructor;
      . apply h; tauto;
      . apply ih.mpr;
        intro ψ hψ;
        apply h;
        tauto;
  | _ => simp;

lemma iff_mem₂_conj {Γ : List _} : ⋀Γ ∈ t.1.2 ↔ (∃ φ ∈ Γ, φ ∈ t.1.2) := by
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

omit [DecidableEq α] [Encodable α] in
private lemma of_mem₁_or : φ ⋎ ψ ∈ t.1.1 → (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push_neg at hC;
  have : φ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.1;
  have : ψ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.2;
  have : 𝓢 ⊢! ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := by simp;
  have : 𝓢 ⊬ ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := t.consistent (by simp_all) (by simp_all);
  contradiction;

private lemma of_mem₂_or : φ ⋎ ψ ∈ t.1.2 → (φ ∈ t.1.2 ∧ ψ ∈ t.1.2) := by
  contrapose;
  suffices (φ ∉ t.1.2 ∨ ψ ∉ t.1.2) → φ ⋎ ψ ∉ t.1.2 by tauto;
  rintro (hφ | hψ);
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₁! $ iff_not_mem₂_mem₁.mp hφ;
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₂! $ iff_not_mem₂_mem₁.mp hψ;

lemma iff_mem₁_or : φ ⋎ ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_or;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₂_or $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor <;> { apply iff_not_mem₁_mem₂.mpr; assumption; };

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

omit [Encodable α] in
private lemma of_mem₁_imp : φ ➝ ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push_neg at hC;
  exact hC.2 $ mdp_mem₁ h $ iff_not_mem₂_mem₁.mp hC.1

private lemma of_mem₂_imp : φ ➝ ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  intro h;
  by_contra hC;
  replace hC := not_and_or.mp hC;
  rcases hC with (hφ | hψ);
  . have : φ ⋎ (φ ➝ ψ) ∈ t.1.1 := iff_provable_mem₁.mp (A!_replace_right lem! CNC!) t;
    rcases of_mem₁_or this with (_ | _);
    . contradiction;
    . have := iff_not_mem₁_mem₂.mpr h;
      contradiction;
  . have : ψ ➝ (φ ➝ ψ) ∈ t.1.1 := iff_provable_mem₁.mp imply₁! t;
    have : φ ➝ ψ ∉ t.1.2 := iff_not_mem₂_mem₁.mpr $ mdp_mem₁ this (iff_not_mem₂_mem₁.mp hψ);
    contradiction;

lemma iff_mem₁_imp : φ ➝ ψ ∈ t.1.1 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_imp;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₂_imp $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor;
    . exact iff_not_mem₂_mem₁.mpr hφ;
    . exact iff_not_mem₁_mem₂.mpr hψ;

lemma iff_mem₂_imp : φ ➝ ψ ∈ t.1.2 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
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

lemma iff_mem₁_neg : ∼φ ∈ t.1.1 ↔ φ ∈ t.1.2 := by
  constructor;
  . apply of_mem₁_neg;
  . contrapose;
    intro h;
    exact iff_not_mem₂_mem₁.mpr $ of_mem₂_neg $ iff_not_mem₁_mem₂.mp h

lemma iff_mem₂_neg : ∼φ ∈ t.1.2 ↔ φ ∈ t.1.1 := by
  constructor;
  . apply of_mem₂_neg;
  . contrapose;
    intro h;
    exact iff_not_mem₁_mem₂.mpr $ of_mem₁_neg $ iff_not_mem₂_mem₁.mp h


omit [Entailment.Modal.K 𝓢] [DecidableEq α] [Encodable α] in
private lemma of_mem₁_multibox : (□^[n]φ ∈ t.1.1) → (∀ {t' : MaximalConsistentTableau 𝓢}, (□''⁻¹^[n]t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := by
  intro h t' ht';
  apply ht';
  tauto;

private lemma of_mem₂_multibox : (□^[n]φ ∈ t.1.2) → (∃ t' : MaximalConsistentTableau 𝓢, (□''⁻¹^[n]t.1.1 ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := by
  intro h;
  obtain ⟨t', ht'⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹^[n]t.1.1, {φ}⟩) $ by
    intro Γ Δ hΓ hΔ;
    by_contra hC;
    have h₁ : 𝓢 ⊢! ⋀□'^[n]Γ ➝ □^[n]⋀Γ := collect_multibox_conj!
    have : 𝓢 ⊢! ⋀□'^[n]Γ ➝ □^[n]φ := C!_trans h₁ (imply_multibox_distribute'! $ C!_trans hC (left_Disj₂!_intro' hΔ));
    have : 𝓢 ⊬ ⋀□'^[n]Γ ➝ ⋁[□^[n]φ] := t.consistent (Γ := □'^[n]Γ) (Δ := [□^[n]φ]) ?_ ?_;
    contradiction;
    . rintro ψ hψ;
      obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_multibox hψ;
      exact hΓ ξ hξ;
    . simpa;
  use t';
  constructor;
  . exact ht'.1;
  . apply ht'.2;
    tauto;

lemma iff_mem₁_multibox : (□^[n]φ ∈ t.1.1) ↔ (∀ {t' : MaximalConsistentTableau 𝓢}, (□''⁻¹^[n]t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := by
  constructor;
  . apply of_mem₁_multibox;
  . contrapose;
    push_neg;
    intro hφ;
    obtain ⟨t', ht'₁, ht'₂⟩ := of_mem₂_multibox $ iff_not_mem₁_mem₂.mp hφ;
    use t';
    constructor;
    . exact ht'₁;
    . exact iff_not_mem₁_mem₂.mpr ht'₂;

lemma iff_mem₁_box : (□φ ∈ t.1.1) ↔ (∀ {t' : MaximalConsistentTableau 𝓢}, (□''⁻¹t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := iff_mem₁_multibox (n := 1)

lemma iff_mem₂_multibox : (□^[n]φ ∈ t.1.2) ↔ (∃ t' : MaximalConsistentTableau 𝓢, (□''⁻¹^[n]t.1.1 ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := by
  constructor;
  . apply of_mem₂_multibox;
  . contrapose;
    push_neg;
    intro hφ t' ht';
    exact iff_not_mem₂_mem₁.mpr $ of_mem₁_multibox (iff_not_mem₂_mem₁.mp hφ) ht';

lemma iff_mem₂_box : (□φ ∈ t.1.2) ↔ (∃ t' : MaximalConsistentTableau 𝓢, (□''⁻¹t.1.1 ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := iff_mem₂_multibox (n := 1)

end Saturated


section

lemma _root_.Set.exists_of_ne {s t : Set α} (h : s ≠ t) : ∃ x, ((x ∈ s ∧ x ∉ t) ∨ (x ∉ s ∧ x ∈ t)) := by
  revert h;
  contrapose;
  push_neg;
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

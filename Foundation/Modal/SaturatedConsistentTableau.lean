import Foundation.Modal.Formula
import Foundation.Modal.Entailment.K

namespace LO.Modal

open Entailment

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}

def Tableau (α : Type u) := Set (Formula α) × Set (Formula α)

namespace Tableau

variable {φ ψ: Formula α} {T U : FormulaSet α} {t u : Tableau α}

def Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ t.1) → (∀ φ ∈ Δ, φ ∈ t.2) → 𝓢 ⊬ ⋀Γ ➝ ⋁Δ

abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬Consistent 𝓢 t

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩
@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma not_mem₂ (hCon : t.Consistent 𝓢) {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1) (h : 𝓢 ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.2 := by
  by_contra hC;
  have : 𝓢 ⊢! ⋀Γ ➝ ⋁[ψ] := by simpa;
  have : 𝓢 ⊬ ⋀Γ ➝ ⋁[ψ] := hCon (by aesop) (by aesop);
  contradiction;


section

variable [Entailment.K 𝓢]

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨φ, hp⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hp;
  unfold Consistent at hCon;
  have : 𝓢 ⊬ ⋀[φ] ➝ ⋁[φ] := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : 𝓢 ⊢! ⋀[φ] ➝ ⋁[φ] := by simp;
  contradiction;

variable [DecidableEq α]

lemma iff_consistent_insert₁
  : Tableau.Consistent 𝓢 ((insert φ T), U) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ T) → (∀ φ ∈ Δ, φ ∈ U) → 𝓢 ⊬ φ ⋏ ⋀Γ ➝ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : 𝓢 ⊬ ⋀(φ :: Γ) ➝ ⋁Δ := h (by simp; intro ψ hψ; right; exact hΓ ψ hψ;) hΔ;
    have : 𝓢 ⊢! ⋀(φ :: Γ) ➝ ⋁Δ := iff_imply_left_cons_conj'!.mpr hC;
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
    have : 𝓢 ⊢! φ ⋏ ⋀(Γ.remove φ) ➝ ⋁Δ := imp_trans''! and_comm! $ imply_left_remove_conj! (φ := φ) hC;
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
    have : 𝓢 ⊢! ⋀Γ ➝ ⋁(φ :: Δ) := implyRight_cons_disj!.mpr hC;
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
    have : 𝓢 ⊢! ⋀Γ ➝ φ ⋎ ⋁(Δ.remove φ) := imp_trans''! hC $ forthback_disj_remove;
    contradiction;

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
      simp at h;
      sorry;
      -- exact or_cases! (χ := φ) (by simp) (by simp) (h ⨀ (by simp))
    . contrapose;
      push_neg;
      intro h;
      use [], [];
      refine ⟨by tauto, by tauto, ?_⟩;
      simp only [List.conj₂_nil, List.disj₂_nil, not_not];
      apply imply₁'!;
      apply or₁'! (by simpa using h);


lemma iff_not_consistent_insert₂ : Tableau.Inconsistent 𝓢 (T, (insert φ U)) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ 𝓢 ⊢! ⋀Γ ➝ φ ⋎ ⋁Δ := by
  unfold Tableau.Inconsistent;
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₂.mp;


section Consistent

variable {t : Tableau α}

lemma consistent_either (hCon : t.Consistent 𝓢) (φ : Formula α) : Tableau.Consistent 𝓢 ((insert φ t.1), t.2) ∨ Tableau.Consistent 𝓢 (t.1, (insert φ t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_inconsistent_insert₁.mp hC₁;
  replace h₁ := imply_left_and_comm'! h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;

  have : 𝓢 ⊢! ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := imp_trans''! (and₁'! iff_concat_conj!) $ imp_trans''! (cut! h₁ h₂) (and₂'! iff_concact_disj!);
  have : 𝓢 ⊬ ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := hCon (by simp; rintro ψ (hq₁ | hq₂); exact hΓ₁ ψ hq₁; exact hΓ₂ ψ hq₂) (by simp; rintro ψ (hq₁ | hq₂); exact hΔ₁ ψ hq₁; exact hΔ₂ ψ hq₂);
  contradiction;

end Consistent

end


def Saturated (t : Tableau α) := ∀ φ : Formula α, φ ∈ t.1 ∨ φ ∈ t.2

section Saturated

variable [Entailment.K 𝓢]
variable {t : Tableau α}

lemma mem₂_of_not_mem₁ (hSat : Saturated t) : φ ∉ t.1 → φ ∈ t.2 := by
  intro h;
  cases (hSat φ) with
  | inl h' => exact absurd h' h;
  | inr _ => assumption;

lemma mem₁_of_not_mem₂ (hSat : Saturated t) : φ ∉ t.2 → φ ∈ t.1 := by
  intro h;
  cases (hSat φ) with
  | inl _ => assumption;
  | inr h' => exact absurd h' h;

lemma iff_not_mem₁_mem₂ (hCon : t.Consistent 𝓢) (hSat : Saturated t) : φ ∉ t.1 ↔ φ ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hSat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma iff_not_mem₂_mem₁ (hCon : t.Consistent 𝓢) (hSat : Saturated t) : φ ∉ t.2 ↔ φ ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hSat;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon;

lemma saturated_duality
  {t₁ t₂ : Tableau α}
  (hCon₁ : t₁.Consistent 𝓢) (hCon₂ : t₂.Consistent 𝓢)
  (hSat₁ : Saturated t₁) (hSat₂ : Saturated t₂)
  : t₁.1 = t₂.1 ↔ t₁.2 = t₂.2 := by
  constructor;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply iff_not_mem₁_mem₂ hCon₂ hSat₂ |>.mp; rw [←h];
      apply iff_not_mem₁_mem₂ hCon₁ hSat₁ |>.mpr hp;
    . intro φ hp;
      apply iff_not_mem₁_mem₂ hCon₁ hSat₁ |>.mp; rw [h];
      apply iff_not_mem₁_mem₂ hCon₂ hSat₂ |>.mpr hp;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro φ hp;
      apply iff_not_mem₂_mem₁ hCon₂ hSat₂ |>.mp; rw [←h];
      apply iff_not_mem₂_mem₁ hCon₁ hSat₁ |>.mpr hp;
    . intro φ hp;
      apply iff_not_mem₂_mem₁ hCon₁ hSat₁ |>.mp; rw [h];
      apply iff_not_mem₂_mem₁ hCon₂ hSat₂ |>.mpr hp;

end Saturated

lemma consistent_empty [Entailment.K 𝓢] [DecidableEq α] [H_consis : Entailment.Consistent 𝓢] : Consistent 𝓢 ⟨∅, ∅⟩ := by
  intro Γ Δ hΓ hΔ;
  replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  replace hΔ : Δ = [] := List.eq_nil_iff_forall_not_mem.mpr hΔ;
  subst hΓ hΔ;
  by_contra hC;
  simp only [List.conj₂_nil, List.disj₂_nil] at hC;
  obtain ⟨ψ, hψ⟩ := H_consis.exists_unprovable;
  have : 𝓢 ⊢! ψ := efq'! (hC ⨀ imp_id!);
  contradiction;


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

def lindenbaum_saturated [Encodable α] (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_saturated 𝓢 t


variable {𝓢}

@[simp] lemma eq_lindenbaum_indexed_zero [Encodable α] {t : Tableau α} : t[0] = t := by simp [lindenbaum_indexed]

lemma consistent_lindenbaum_next [Entailment.K 𝓢] (consistent : t.Consistent 𝓢) (φ : Formula α) : (t.lindenbaum_next 𝓢 φ).Consistent 𝓢 := by
  unfold lindenbaum_next;
  split;
  . assumption;
  . rcases (consistent_either consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma consistent_lindenbaum_indexed_succ [Entailment.K 𝓢] {i : ℕ} : Consistent 𝓢 t[i] → Consistent 𝓢 t[i + 1] := by
  simp only [lindenbaum_indexed];
  split;
  . intro h;
    apply consistent_lindenbaum_next (𝓢 := 𝓢);
    assumption;
  . tauto;

lemma either_mem_lindenbaum_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp only [lindenbaum_indexed, encodek, lindenbaum_next];
  split <;> tauto;

lemma consistent_lindenbaum_indexed [Entailment.K 𝓢] (consistent : t.Consistent 𝓢) (i : ℕ) : t[i].Consistent 𝓢 := by
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

lemma exists_consistent_saturated_tableau [Entailment.K 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (Tableau.Consistent 𝓢 u) ∧ (Saturated u) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?saturated⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case saturated =>
    intro φ;
    rcases either_mem_lindenbaum_indexed (𝓢 := 𝓢) t φ with (h | h);
    . left; simp only [lindenbaum_saturated, Set.mem_iUnion]; use (encode φ + 1);
    . right; simp only [lindenbaum_saturated, Set.mem_iUnion]; use (encode φ + 1);
  case consistent =>
    intro Γ Δ hΓ hΔ;
    simp_all only [lindenbaum_saturated, Set.mem_iUnion];
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


def SaturatedConsistentTableau (𝓢 : S) := {t : Tableau α // Saturated t ∧ t.Consistent 𝓢}

namespace SaturatedConsistentTableau

lemma consistent (t : SaturatedConsistentTableau 𝓢) : Consistent 𝓢 t.1 := t.2.2

lemma saturated (t : SaturatedConsistentTableau 𝓢) : Saturated t.1 := t.2.1

variable {t₀ : Tableau α} {φ ψ : Formula α}

lemma lindenbaum [Entailment.K 𝓢] [Encodable α] (hCon : t₀.Consistent 𝓢) : ∃ (t : SaturatedConsistentTableau 𝓢), t₀ ⊆ t.1 := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [Entailment.Consistent 𝓢] [Entailment.K 𝓢] [DecidableEq α] [Encodable α] : Nonempty (SaturatedConsistentTableau 𝓢) := ⟨lindenbaum consistent_empty |>.choose⟩

variable {t t₁ t₂ : SaturatedConsistentTableau 𝓢}

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1.1) (h : 𝓢 ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.1.2 := t.1.not_mem₂ t.consistent hΓ h

variable [Entailment.K 𝓢]

lemma disjoint : Disjoint t.1.1 t.1.2 := t.1.disjoint_of_consistent t.2.2

lemma iff_not_mem₁_mem₂ : φ ∉ t.1.1 ↔ φ ∈ t.1.2 := Tableau.iff_not_mem₁_mem₂ t.consistent t.saturated

lemma iff_not_mem₂_mem₁ : φ ∉ t.1.2 ↔ φ ∈ t.1.1 := Tableau.iff_not_mem₂_mem₁ t.consistent t.saturated

@[simp]
lemma neither : ¬(φ ∈ t.1.1 ∧ φ ∈ t.1.2) := by
  push_neg;
  intro h;
  exact iff_not_mem₂_mem₁.mpr h;

lemma saturated_duality: t.1.1 = t₂.1.1 ↔ t.1.2 = t₂.1.2 := Tableau.saturated_duality t.consistent t₂.consistent t.saturated t₂.saturated

lemma equality_of₁ (e₁ : t₁.1.1 = t₂.1.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (saturated_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.1, t₁.saturated, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.1, t₂.saturated, t₂.consistent⟩ := by simp [e];
    _  = t₂                                  := by rfl;

lemma equality_of₂ (e₂ : t₁.1.2 = t₂.1.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂

lemma mdp_mem₁ (hp₁ : φ ∈ t.1.1) (h : 𝓢 ⊢! φ ➝ ψ) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hq₂;
  have : 𝓢 ⊬ φ ➝ ψ := by simpa using t.consistent (Γ := [φ]) (Δ := [ψ]) (by simpa) (by simpa);
  contradiction;

lemma mdp_mem₁Aux [DecidableEq α] (h : φ ➝ ψ ∈ t.1.1) (hp : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  have : 𝓢 ⊬ (φ ⋏ (φ ➝ ψ)) ➝ ψ := t.consistent (Γ := [φ, φ ➝ ψ]) (Δ := [ψ]) (by aesop) (by simpa);
  have : 𝓢 ⊢! (φ ⋏ (φ ➝ ψ)) ➝ ψ := mdp_in!
  contradiction;

@[simp]
lemma mem₁_verum : ⊤ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  have : 𝓢 ⊬ ⋀[] ➝ ⋁[⊤] := t.consistent (by simp) (by simpa);
  have : 𝓢 ⊢! ⋀[] ➝ ⋁[⊤] := by simp;
  contradiction;

@[simp]
lemma not_mem₂_verum : ⊤ ∉ t.1.2 := by
  apply iff_not_mem₂_mem₁.mpr;
  exact mem₁_verum;

@[simp]
lemma not_mem₁_falsum : ⊥ ∉ t.1.1 := by
  by_contra hC;
  have : 𝓢 ⊬ ⋀[⊥] ➝ ⋁[] := t.consistent (by simpa) (by simp);
  have : 𝓢 ⊢! ⋀[⊥] ➝ ⋁[] := by simp;
  contradiction;

@[simp]
lemma mem₂_falsum : ⊥ ∈ t.1.2 := by
  apply iff_not_mem₁_mem₂.mp;
  exact not_mem₁_falsum;

lemma mem₁_of_provable : 𝓢 ⊢! φ → φ ∈ t.1.1 := by
  intro h;
  exact mdp_mem₁ mem₁_verum $ imply₁'! h;

lemma iff_mem₁_neg [DecidableEq α] : ∼φ ∈ t.1.1 ↔ φ ∈ t.1.2 := by
  constructor;
  . intro hnφ;
    by_contra hφ;
    replace hφ := iff_not_mem₂_mem₁.mp hφ;
    exact not_mem₁_falsum $ mdp_mem₁Aux hnφ hφ;
  . intro hφ;
    by_contra hnφ;
    replace hnφ := iff_not_mem₁_mem₂.mp hnφ;
    have := t.consistent (Γ := []) (Δ := [φ, ∼φ]) (by simp) (by simp_all);
    have : 𝓢 ⊢! ⊤ ➝ ⋁[φ, ∼φ] := imply₁'! lem!
    contradiction;

lemma iff_mem₂_neg [DecidableEq α] : ∼φ ∈ t.1.2 ↔ φ ∈ t.1.1 := by
  constructor;
  . intro h;
    apply iff_not_mem₂_mem₁.mp;
    apply iff_mem₁_neg.not.mp;
    apply iff_not_mem₁_mem₂.mpr;
    exact h;
  . intro h;
    apply iff_not_mem₁_mem₂.mp;
    apply iff_mem₁_neg.not.mpr;
    apply iff_not_mem₂_mem₁.mpr;
    exact h;

lemma of_mem₁_imp [DecidableEq α] : φ ➝ ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push_neg at hC;
  have : ψ ∈ t.1.1 := mdp_mem₁Aux h $ iff_not_mem₂_mem₁.mp hC.1;
  have : ψ ∉ t.1.1 := iff_not_mem₁_mem₂.mpr $ iff_not_mem₁_mem₂.mp hC.2;
  contradiction;

lemma of_mem₂_imp [DecidableEq α] : φ ➝ ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  contrapose;
  intro h;
  replace h := not_and_or.mp h;
  rcases h with (hφ | hψ);
  . sorry;
  . sorry;

lemma iff_mem₁_imp' [DecidableEq α] : φ ➝ ψ ∈ t.1.1 ↔ (φ ∈ t.1.1 → ψ ∈ t.1.1) := by
  constructor;
  . intro h;
    by_contra hC;
    push_neg at hC;
    have : ψ ∈ t.1.1 := mdp_mem₁Aux h hC.1;
    have : ψ ∉ t.1.1 := iff_not_mem₁_mem₂.mpr $ iff_not_mem₁_mem₂.mp hC.2;
    contradiction
  . intro h;
    replace h := imp_iff_or_not.mp h;
    rcases h with (hψ | hφ);
    . exact mdp_mem₁ hψ imply₁!;
    . sorry;

lemma iff_mem₁_imp [DecidableEq α] : φ ➝ ψ ∈ t.1.1 ↔ φ ∈ t.1.2 ∨ ψ ∈ t.1.1 := by
  constructor;
  . intro h;
    by_contra hC;
    push_neg at hC;
    have : φ ∈ t.1.1 := iff_not_mem₂_mem₁.mp hC.1;
    have : ψ ∈ t.1.1 := mdp_mem₁Aux h this;
    have : ψ ∉ t.1.1 := iff_not_mem₁_mem₂.mpr $ iff_not_mem₁_mem₂.mp hC.2;
    contradiction
  . rintro (hφ | hψ);
    . sorry;
    . exact mdp_mem₁ hψ imply₁!;

lemma iff_mem₂_imp [DecidableEq α] : φ ➝ ψ ∈ t.1.2 ↔ φ ∈ t.1.1 ∧ ψ ∈ t.1.2 := by
  constructor;
  . contrapose;
    suffices (φ ∉ t.1.1 ∨ ψ ∉ t.1.2) → φ ➝ ψ ∉ t.1.2 by tauto;
    rintro (hφ | hψ);
    . apply iff_not_mem₂_mem₁.mpr;
      apply iff_mem₁_imp.mpr;
      left;
      exact iff_not_mem₁_mem₂.mp hφ;
    . apply iff_not_mem₂_mem₁.mpr;
      apply iff_mem₁_imp.mpr;
      right;
      exact iff_not_mem₂_mem₁.mp hψ;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    apply iff_not_mem₂_mem₁.mpr;
    replace hφψ := iff_not_mem₂_mem₁.mp hφψ;
    exact mdp_mem₁Aux hφψ hφ;

/-
lemma iff_mem₁_neg [DecidableEq α] : ∼φ ∈ t.1.1 ↔ φ ∈ t.1.2 := by
  constructor;
  . intro h;
    rcases iff_mem₁_imp.mp h with (h | h);
    . assumption;
    . exfalso;
      exact not_mem₁_falsum h;
  . intro h;
    apply iff_mem₁_imp.mpr;
    left;
    exact h;

lemma iff_mem₂_neg [DecidableEq α] : ∼φ ∈ t.1.2 ↔ φ ∈ t.1.1 := by
  constructor;
  . intro h;
    apply iff_not_mem₂_mem₁.mp;
    apply iff_mem₁_neg.not.mp;
    apply iff_not_mem₁_mem₂.mpr;
    exact h;
  . intro h;
    apply iff_not_mem₁_mem₂.mp;
    apply iff_mem₁_neg.not.mpr;
    apply iff_not_mem₂_mem₁.mpr;
    exact h;
-/

@[simp]
lemma iff_mem₁_and : φ ⋏ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∧ ψ ∈ t.1.1 := by
  constructor;
  . intro h; constructor <;> exact mdp_mem₁ h (by simp)
  . rintro ⟨hp, hq⟩;
    apply iff_not_mem₂_mem₁.mp;
    by_contra hC;
    have : 𝓢 ⊢! ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := by simp;
    have : 𝓢 ⊬ ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := t.consistent (by simp_all) (by simp_all);
    contradiction;

@[simp]
lemma iff_mem₂_and : φ ⋏ ψ ∈ t.1.2 ↔ φ ∈ t.1.2 ∨ ψ ∈ t.1.2 := by
  constructor;
  . contrapose;
    push_neg;
    rintro ⟨hφ, hψ⟩;
    apply iff_not_mem₂_mem₁.mpr;
    apply iff_mem₁_and.mpr;
    constructor;
    . exact iff_not_mem₂_mem₁.mp hφ;
    . exact iff_not_mem₂_mem₁.mp hψ;
  . contrapose;
    push_neg;
    intro h;
    constructor;
    . apply iff_not_mem₂_mem₁.mpr;
      exact iff_mem₁_and.mp (iff_not_mem₂_mem₁.mp h) |>.1;
    . apply iff_not_mem₂_mem₁.mpr;
      exact iff_mem₁_and.mp (iff_not_mem₂_mem₁.mp h) |>.2;

@[simp]
lemma iff_mem₁_or : φ ⋎ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∨ ψ ∈ t.1.1 := by
  constructor;
  . intro h;
    by_contra hC; push_neg at hC;
    have : φ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.1;
    have : ψ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.2;
    have : 𝓢 ⊢! ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := by simp;
    have : 𝓢 ⊬ ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp_mem₁ h or₁!
    | inr h => exact mdp_mem₁ h or₂!

@[simp]
lemma iff_mem₂_or : φ ⋎ ψ ∈ t.1.2 ↔ φ ∈ t.1.2 ∧ ψ ∈ t.1.2 := by
  constructor;
  . contrapose;
    suffices (φ ∉ t.1.2 ∨ ψ ∉ t.1.2) → φ ⋎ ψ ∉ t.1.2 by tauto;
    rintro (hφ | hψ);
    . apply iff_not_mem₂_mem₁.mpr;
      apply iff_mem₁_or.mpr;
      left;
      exact iff_not_mem₂_mem₁.mp hφ;
    . apply iff_not_mem₂_mem₁.mpr;
      apply iff_mem₁_or.mpr;
      right;
      exact iff_not_mem₂_mem₁.mp hψ;
  . contrapose;
    intro h;
    suffices φ ∉ t.1.2 ∨ ψ ∉ t.1.2 by tauto;
    rcases iff_mem₁_or.mp $ iff_not_mem₂_mem₁.mp h with (hφ | hψ);
    . left;
      exact iff_not_mem₂_mem₁.mpr hφ;
    . right;
      exact iff_not_mem₂_mem₁.mpr hψ;

@[simp]
lemma iff_mem₁_conj {Γ : List (Formula α)} : ⋀Γ ∈ t.1.1 ↔ ∀ φ ∈ Γ, φ ∈ t.1.1 := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle φ => simp;
  | hcons φ Γ Γ_nil ih =>
    simp only [(List.conj₂_cons_nonempty Γ_nil), List.mem_cons];
    constructor;
    . rintro h φ (rfl | hp);
      . exact iff_mem₁_and.mp h |>.1;
      . exact ih.mp (iff_mem₁_and.mp h |>.2) _ hp;
    . intro h;
      apply iff_mem₁_and.mpr;
      simp_all;

lemma not_mem₁_neg_of_mem₁ [DecidableEq α] : φ ∈ t.1.1 → ∼φ ∉ t.1.1 := by
  intro hp;
  by_contra hnp;
  have := iff_mem₁_and.mpr ⟨hp, hnp⟩;
  have : ⊥ ∈ t.1.1 := mdp_mem₁ this intro_bot_of_and!;
  have : ⊥ ∉ t.1.1 := not_mem₁_falsum
  contradiction;

lemma mem₂_neg_of_mem₁ [DecidableEq α] : φ ∈ t.1.1 → ∼φ ∈ t.1.2 := by
  intro h;
  exact iff_not_mem₁_mem₂ (φ := ∼φ) (t := t) |>.mp $ not_mem₁_neg_of_mem₁ h;


variable [Encodable α]

lemma iff_multibox_mem₁ : (□^[n]φ ∈ t.1.1) ↔ (∀ {t' : SaturatedConsistentTableau 𝓢}, (□''⁻¹^[n]t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := by
  constructor;
  . intro h t' ht';
    apply ht';
    tauto;
  . contrapose;
    push_neg;
    intro h;
    obtain ⟨t', ht'⟩ := lindenbaum (𝓢 := 𝓢) (t₀ := ⟨□''⁻¹^[n]t.1.1, {φ}⟩) $ by
      intro Γ Δ hΓ hΔ;
      by_contra hC;
      sorry;
    use t';
    constructor;
    . exact ht'.1;
    . apply iff_not_mem₁_mem₂.mpr;
      apply ht'.2;
      tauto_set;

lemma iff_box_mem₁ : (□φ ∈ t.1.1) ↔ (∀ {t' : SaturatedConsistentTableau 𝓢}, (□''⁻¹t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := iff_multibox_mem₁ (n := 1)

lemma of_box_mem₁ : (□φ ∈ t.1.1) → (∀ {t' : SaturatedConsistentTableau 𝓢}, (□''⁻¹t.1.1 ⊆ t'.1.1) → (φ ∈ t'.1.1)) := iff_multibox_mem₁ (n := 1) |>.mp

lemma of_box_mem₂ : (□φ ∈ t.1.2) → (∃ t' : SaturatedConsistentTableau 𝓢, (□''⁻¹t.1.1 ⊆ t'.1.1) ∧ (φ ∈ t'.1.2)) := by sorry;

end SaturatedConsistentTableau

end LO.Modal

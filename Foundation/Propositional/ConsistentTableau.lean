import Foundation.Propositional.Formula
import Foundation.Logic.HilbertStyle.Supplemental

namespace LO.Propositional

open Entailment FiniteContext
open Formula

variable {α : Type*}
variable {S} [Entailment (Formula α) S]
variable {𝓢 : S}


def Tableau (α : Type u) := Set (Formula α) × Set (Formula α)

namespace Tableau

variable {φ ψ: Formula α} {T U : FormulaSet α} {t u : Tableau α}

abbrev Consistent (𝓢 : S) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ t.1) → (∀ φ ∈ Δ, φ ∈ t.2) → 𝓢 ⊬ ⋀Γ ➝ ⋁Δ

abbrev Inconsistent (𝓢 : S) (t : Tableau α) := ¬Consistent 𝓢 t

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩
@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

lemma not_mem₂ (hCon : t.Consistent 𝓢) {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1) (h : 𝓢 ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.2 := by
  by_contra hC;
  have : 𝓢 ⊢! ⋀Γ ➝ ⋁[ψ] := by simpa;
  have : 𝓢 ⊬ ⋀Γ ➝ ⋁[ψ] := hCon (by aesop) (by aesop);
  contradiction;

section

variable [Entailment.Int 𝓢]

lemma disjoint_of_consistent (hCon : t.Consistent 𝓢) : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨φ, hp⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hp;
  simp [Consistent] at hCon;
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
    have : 𝓢 ⊬ ⋀(φ :: Γ) ➝ ⋁Δ := h (by simp; intro ψ hq; right; exact hΓ ψ hq;) hΔ;
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

lemma iff_not_consistent_insert₁ : ¬Tableau.Consistent 𝓢 ((insert φ T), U) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ 𝓢 ⊢! φ ⋏ ⋀Γ ➝ ⋁Δ := by
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

lemma iff_not_consistent_insert₂ : ¬Tableau.Consistent 𝓢 (T, (insert φ U)) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ 𝓢 ⊢! ⋀Γ ➝ φ ⋎ ⋁Δ := by
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₂.mp;

section Consistent

variable {t : Tableau α}

lemma consistent_either (hCon : t.Consistent 𝓢) (φ : Formula α) : Tableau.Consistent 𝓢 ((insert φ t.1), t.2) ∨ Tableau.Consistent 𝓢 (t.1, (insert φ t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_consistent_insert₁.mp hC₁;
  replace h₁ := left_K!_symm h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;

  have : 𝓢 ⊢! ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := C!_trans (K!_left EConj₂AppendKConj₂Conj₂!) $ C!_trans (cut! h₁ h₂) (K!_right EDisj₂AppendADisj₂Disj₂!);
  have : 𝓢 ⊬ ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := hCon (by simp; rintro ψ (hq₁ | hq₂); exact hΓ₁ ψ hq₁; exact hΓ₂ ψ hq₂) (by simp; rintro ψ (hq₁ | hq₂); exact hΔ₁ ψ hq₁; exact hΔ₂ ψ hq₂);
  contradiction;

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
  replace hΓ : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  replace hΔ : Δ = [] := List.eq_nil_iff_forall_not_mem.mpr hΔ;
  subst hΓ hΔ;
  by_contra hC;
  simp at hC;
  obtain ⟨ψ, hq⟩ := H_consis.exists_unprovable;
  have : 𝓢 ⊢! ψ := of_O! (hC ⨀ C!_id);
  contradiction;

section lindenbaum

variable (𝓢 : S)
variable {t : Tableau α}

open Classical
open Encodable

def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent 𝓢 (insert φ t.1, t.2) then (insert φ t.1, t.2) else (t.1, insert φ t.2)

def lindenbaum_next_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
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
  simp [lindenbaum_next];
  split;
  . simpa;
  . rcases (consistent_either consistent φ) with (h | h);
    . contradiction;
    . assumption;

variable [Encodable α]

lemma lindenbaum_next_indexed_parametricConsistent_succ [Entailment.Int 𝓢] {i : ℕ} : Consistent 𝓢 t[i] → Consistent 𝓢 t[i + 1] := by
  simp [lindenbaum_next_indexed];
  split;
  . intro h;
    apply next_parametericConsistent (𝓢 := 𝓢);
    assumption;
  . tauto;

lemma mem_lindenbaum_next_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp [lindenbaum_next_indexed, lindenbaum_next];
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

lemma exists_parametricConsistent_saturated_tableau [Entailment.Int 𝓢] (hCon : t.Consistent 𝓢) : ∃ u, t ⊆ u ∧ (Tableau.Consistent 𝓢 u) ∧ (Saturated u) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?saturated⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case saturated =>
    intro φ;
    rcases mem_lindenbaum_next_indexed (𝓢 := 𝓢) t φ with (h | h);
    . left; simp [lindenbaum_maximal]; use (encode φ + 1);
    . right; simp [lindenbaum_maximal]; use (encode φ + 1);
  case consistent =>
    intro Γ Δ hΓ hΔ;
    simp_all [lindenbaum_maximal];
    obtain ⟨m, hΓ⟩ : ∃ m, ∀ φ ∈ Γ, φ ∈ t[m].1 := by
      induction Γ with
      | nil => simp;
      | cons φ Γ ih =>
        simp_all;
        obtain ⟨i, hi⟩ := hΓ.1;
        obtain ⟨m, hm⟩ := ih;
        use (i + m);
        constructor;
        . exact lindenbaum_next_indexed_subset₁_of_lt (by simp) hi;
        . intro ψ hq;
          exact lindenbaum_next_indexed_subset₁_of_lt (by simp) $ hm ψ hq;
    obtain ⟨n, hΔ⟩ : ∃ n, ∀ φ ∈ Δ, φ ∈ t[n].2 := by
      induction Δ with
      | nil => simp;
      | cons φ Δ ih =>
        simp_all;
        obtain ⟨i, hi⟩ := hΔ.1;
        obtain ⟨n, hn⟩ := ih;
        use (i + n);
        constructor;
        . exact lindenbaum_next_indexed_subset₂_of_lt (by simp) hi;
        . intro ψ hq;
          exact lindenbaum_next_indexed_subset₂_of_lt (by simp) $ hn ψ hq;
    rcases (lt_trichotomy m n) with hm | hmn | hn;
    . exact lindenbaum_next_indexed_parametricConsistent hCon n (by intro φ hp; exact lindenbaum_next_indexed_subset₁_of_lt hm.le $ hΓ φ hp) hΔ;
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

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1.1) (h : 𝓢 ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.1.2 := t.1.not_mem₂ t.consistent hΓ h

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
    _  = t₂                                  := by rfl;

lemma equality_of₂ (e₂ : t₁.1.2 = t₂.1.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂


section

variable [DecidableEq α] [Encodable α]

lemma iff_provable_include₁ : T *⊢[𝓢]! φ ↔ ∀ t : SaturatedConsistentTableau 𝓢, (T ⊆ t.1.1) → φ ∈ t.1.1 := by
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

lemma iff_provable_mem₁ : 𝓢 ⊢! φ ↔ ∀ t : SaturatedConsistentTableau 𝓢, φ ∈ t.1.1 := by
  constructor;
  . intro h t;
    apply iff_provable_include₁ (T := ∅) |>.mp;
    . exact Context.of! h;
    . simp;
  . intro h;
    exact Context.emptyPrf! $ iff_provable_include₁.mpr $ by tauto;

end





section Saturated

lemma mdp_mem₁_provable (h : 𝓢 ⊢! φ ➝ ψ) (hp₁ : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hq₂;
  have : 𝓢 ⊬ φ ➝ ψ := by simpa using t.consistent (Γ := [φ]) (Δ := [ψ]) (by simpa) (by simpa);
  contradiction;

@[simp] lemma mem₁_verum : ⊤ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  have : 𝓢 ⊬ ⋀[] ➝ ⋁[⊤] := t.consistent (by simp) (by simpa);
  have : 𝓢 ⊢! ⋀[] ➝ ⋁[⊤] := by simp;
  contradiction;

@[simp] lemma not_mem₁_falsum : ⊥ ∉ t.1.1 := by
  by_contra hC;
  have : 𝓢 ⊬ ⋀[⊥] ➝ ⋁[] := t.consistent (by simpa) (by simp);
  have : 𝓢 ⊢! ⋀[⊥] ➝ ⋁[] := by simp;
  contradiction;

lemma mem₁_of_provable : 𝓢 ⊢! φ → φ ∈ t.1.1 := by
  intro h;
  exact mdp_mem₁_provable (C!_of_conseq! h) mem₁_verum;

lemma mdp_mem₁ [DecidableEq α] (h : φ ➝ ψ ∈ t.1.1) (hp : φ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  have : 𝓢 ⊬ (φ ⋏ (φ ➝ ψ)) ➝ ψ := t.consistent (Γ := [φ, φ ➝ ψ]) (Δ := [ψ]) (by aesop) (by simpa);
  have : 𝓢 ⊢! (φ ⋏ (φ ➝ ψ)) ➝ ψ := inner_mdp!
  contradiction;


lemma iff_mem₁_and : φ ⋏ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∧ ψ ∈ t.1.1 := by
  constructor;
  . intro h; constructor <;> exact mdp_mem₁_provable (by simp) h
  . rintro ⟨hp, hq⟩;
    apply iff_not_mem₂_mem₁.mp;
    by_contra hC;
    have : 𝓢 ⊢! ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := by simp;
    have : 𝓢 ⊬ ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := t.consistent (by simp_all) (by simp_all);
    contradiction;

lemma iff_mem₁_conj {Γ : List (Formula α)} : ⋀Γ ∈ t.1.1 ↔ ∀ φ ∈ Γ, φ ∈ t.1.1 := by
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


private lemma of_mem₁_or : φ ⋎ ψ ∈ t.1.1 → (φ ∈ t.1.1 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC; push_neg at hC;
  have : φ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.1;
  have : ψ ∈ t.1.2 := iff_not_mem₁_mem₂.mp hC.2;
  have : 𝓢 ⊢! ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := by simp;
  have : 𝓢 ⊬ ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := t.consistent (by simp_all) (by simp_all);
  contradiction;

private lemma of_mem₂_or : φ ⋎ ψ ∈ t.1.2 → φ ∈ t.1.2 ∧ ψ ∈ t.1.2 := by
  contrapose;
  suffices (φ ∉ t.1.2 ∨ ψ ∉ t.1.2) → φ ⋎ ψ ∉ t.1.2 by tauto;
  rintro (hφ | hψ);
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₁! $ iff_not_mem₂_mem₁.mp hφ;
  . apply iff_not_mem₂_mem₁.mpr;
    exact mdp_mem₁_provable or₂! $ iff_not_mem₂_mem₁.mp hψ;

lemma iff_mem₁_or : φ ⋎ ψ ∈ t.1.1 ↔ φ ∈ t.1.1 ∨ ψ ∈ t.1.1 := by
  constructor;
  . apply of_mem₁_or;
  . intro h;
    cases h with
    | inl h => exact mdp_mem₁_provable or₁! h;
    | inr h => exact mdp_mem₁_provable or₂! h;

lemma iff_mem₂_or : φ ⋎ ψ ∈ t.1.2 ↔ φ ∈ t.1.2 ∧ ψ ∈ t.1.2 := by
  constructor;
  . apply of_mem₂_or;
  . contrapose;
    push_neg;
    intro hφψ hφ;
    rcases iff_mem₁_or.mp $ iff_not_mem₂_mem₁.mp hφψ with (hφ | hψ);
    . have := iff_not_mem₂_mem₁.mpr hφ; contradiction;
    . exact iff_not_mem₂_mem₁.mpr hψ;


private lemma of_mem₁_imp [DecidableEq α] : φ ➝ ψ ∈ t.1.1 → (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  intro h;
  by_contra hC;
  push_neg at hC;
  exact hC.2 $ mdp_mem₁ h $ iff_not_mem₂_mem₁.mp hC.1

private lemma of_mem₂_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ ➝ ψ ∈ t.1.2 → (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  intro h;
  by_contra hC;
  replace hC := not_and_or.mp hC;
  rcases hC with (hφ | hψ);
  . have : φ ⋎ (φ ➝ ψ) ∈ t.1.1 := iff_provable_mem₁.mp (A!_replace_right lem! CNC!) t;
    rcases iff_mem₁_or.mp this with (_ | _);
    . contradiction;
    . have := iff_not_mem₁_mem₂.mpr h;
      contradiction;
  . have : ψ ➝ (φ ➝ ψ) ∈ t.1.1 := iff_provable_mem₁.mp imply₁! t;
    have : φ ➝ ψ ∉ t.1.2 := iff_not_mem₂_mem₁.mpr $ mdp_mem₁ this (iff_not_mem₂_mem₁.mp hψ);
    contradiction;

lemma iff_mem₁_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ ➝ ψ ∈ t.1.1 ↔ (φ ∈ t.1.2 ∨ ψ ∈ t.1.1) := by
  constructor;
  . apply of_mem₁_imp;
  . contrapose;
    push_neg;
    intro hφψ;
    rcases of_mem₂_imp $ iff_not_mem₁_mem₂.mp hφψ with ⟨hφ, hψ⟩;
    constructor;
    . exact iff_not_mem₂_mem₁.mpr hφ;
    . exact iff_not_mem₁_mem₂.mpr hψ;

lemma iff_mem₂_imp [DecidableEq α] [Encodable α] [Entailment.Cl 𝓢] : φ ➝ ψ ∈ t.1.2 ↔ (φ ∈ t.1.1 ∧ ψ ∈ t.1.2) := by
  constructor;
  . apply of_mem₂_imp;
  . contrapose;
    push_neg;
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

lemma mdp₁_mem [DecidableEq α] (hp : φ ∈ t.1.1) (h : φ ➝ ψ ∈ t.1.1) : ψ ∈ t.1.1 := by
  apply iff_not_mem₂_mem₁.mp;
  by_contra hC;
  have : 𝓢 ⊬ (φ ⋏ (φ ➝ ψ)) ➝ ψ := t.consistent (Γ := [φ, φ ➝ ψ]) (Δ := [ψ]) (by aesop) (by simpa);
  have : 𝓢 ⊢! (φ ⋏ (φ ➝ ψ)) ➝ ψ := inner_mdp!
  contradiction;

end Saturated

end SaturatedConsistentTableau

end LO.Propositional

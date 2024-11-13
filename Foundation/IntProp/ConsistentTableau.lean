import Foundation.IntProp.Deduction

set_option autoImplicit false
universe u v

namespace LO.IntProp

open System FiniteContext
open Formula

variable {α : Type u}
variable {H : Hilbert α}

def Tableau (α : Type u) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

def Consistent (H : Hilbert α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ t.1) → (∀ φ ∈ Δ, φ ∈ t.2) → H ⊬ ⋀Γ ➝ ⋁Δ

variable {φ ψ: Formula α} {T U : Theory α}

section

variable [DecidableEq α]

lemma iff_consistent_insert₁ : Tableau.Consistent H ((insert φ T), U) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ T) → (∀ φ ∈ Δ, φ ∈ U) → H ⊬ φ ⋏ ⋀Γ ➝ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : H ⊬ ⋀(φ :: Γ) ➝ ⋁Δ := h (by simp; intro ψ hq; right; exact hΓ ψ hq;) hΔ;
    have : H ⊢! ⋀(φ :: Γ) ➝ ⋁Δ := iff_imply_left_cons_conj'!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all only [Set.mem_insert_iff];
    have : H ⊬ φ ⋏ ⋀(Γ.remove φ) ➝ ⋁Δ := h (by
      intro ψ hq;
      have := by simpa using hΓ ψ $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    ) hΔ;
    by_contra hC;
    have : H ⊢! φ ⋏ ⋀(Γ.remove φ) ➝ ⋁Δ := imp_trans''! and_comm! $ imply_left_remove_conj! (φ := φ) hC;
    contradiction;

lemma iff_not_consistent_insert₁ : ¬Tableau.Consistent H ((insert φ T), U) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ H ⊢! φ ⋏ ⋀Γ ➝ ⋁Δ := by
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₁.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₁.mp;

variable [H.IncludeEFQ]

lemma iff_consistent_insert₂ : Tableau.Consistent H (T, (insert φ U)) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ φ ∈ Γ, φ ∈ T) → (∀ φ ∈ Δ, φ ∈ U) → H ⊬ ⋀Γ ➝ φ ⋎ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : H ⊬ ⋀Γ ➝ ⋁(φ :: Δ) := h hΓ (by simp; intro ψ hq; right; exact hΔ ψ hq);
    have : H ⊢! ⋀Γ ➝ ⋁(φ :: Δ) := implyRight_cons_disj!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all;
    have : H ⊬ ⋀Γ ➝ φ ⋎ ⋁(Δ.remove φ) := h hΓ (by
      intro ψ hq;
      have := by simpa using hΔ ψ $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have : H ⊢! ⋀Γ ➝ φ ⋎ ⋁(Δ.remove φ) := imp_trans''! hC $ forthback_disj_remove;
    contradiction;


lemma iff_not_consistent_insert₂ : ¬Tableau.Consistent H (T, (insert φ U)) ↔ ∃ Γ Δ : List (Formula α), (∀ φ ∈ Γ, φ ∈ T) ∧ (∀ φ ∈ Δ, φ ∈ U) ∧ H ⊢! ⋀Γ ➝ φ ⋎ ⋁Δ := by
  constructor;
  . contrapose; push_neg; apply iff_consistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_consistent_insert₂.mp;

section Consistent

variable {t : Tableau α}

lemma consistent_either (hCon : Tableau.Consistent H t) (φ : Formula α) : Tableau.Consistent H ((insert φ t.1), t.2) ∨ Tableau.Consistent H (t.1, (insert φ t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_consistent_insert₁.mp hC₁;
  replace h₁ := imply_left_and_comm'! h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_consistent_insert₂.mp hC₂;

  have : H ⊢! ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := imp_trans''! (and₁'! iff_concat_conj!) $ imp_trans''! (cut! h₁ h₂) (and₂'! iff_concact_disj!);
  have : H ⊬ ⋀(Γ₁ ++ Γ₂) ➝ ⋁(Δ₁ ++ Δ₂) := hCon (by simp; rintro ψ (hq₁ | hq₂); exact hΓ₁ ψ hq₁; exact hΓ₂ ψ hq₂) (by simp; rintro ψ (hq₁ | hq₂); exact hΔ₁ ψ hq₁; exact hΔ₂ ψ hq₂);
  contradiction;

omit [DecidableEq α] [H.IncludeEFQ] in
lemma disjoint_of_consistent (hCon : Tableau.Consistent H t) : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨φ, hp⟩ := Set.nonempty_def.mp $ Set.nonempty_iff_ne_empty.mpr hp;
  simp [Consistent] at hCon;
  have : H ⊬ ⋀[φ] ➝ ⋁[φ] := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : H ⊢! ⋀[φ] ➝ ⋁[φ] := by simp;
  contradiction;

omit [DecidableEq α] [H.IncludeEFQ] in
lemma not_mem₂ (hCon : Tableau.Consistent H t) {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.1) (h : H ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.2 := by
  by_contra hC;
  have : H ⊢! ⋀Γ ➝ ⋁[ψ] := by simpa;
  have : H ⊬ ⋀Γ ➝ ⋁[ψ] := hCon (by aesop) (by aesop);
  contradiction;

end Consistent

end


abbrev Saturated (t : Tableau α) := ∀ φ : Formula α, φ ∈ t.1 ∨ φ ∈ t.2

section Saturated

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


lemma not_mem₁_iff_mem₂ (hCon : Tableau.Consistent H t) (hMat : Saturated t) : φ ∉ t.1 ↔ φ ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma not_mem₂_iff_mem₁ (hCon : Tableau.Consistent H t) (hMat : Saturated t) : φ ∉ t.2 ↔ φ ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hMat;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon;

lemma saturated_duality
  {t₁ t₂ : Tableau α}
  (ct₁ : Tableau.Consistent H t₁) (ct₂ : Tableau.Consistent H t₂)
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

variable [H.IncludeEFQ]

lemma self_consistent [h : H.Consistent] : Tableau.Consistent H (H.axioms, ∅) := by
  intro Γ Δ hΓ hΔ;
  replace hΔ : Δ = [] := List.nil_iff.mpr hΔ;
  obtain ⟨ψ, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : H ⊢! ψ := by
    subst hΔ;
    simp at hC;
    exact imp_trans''! hC efq! ⨀ (by
      apply iff_provable_list_conj.mpr;
      intro φ hφ;
      exact Hilbert.Deduction.eaxm! $ hΓ _ hφ;
    );
  contradiction;

section lindenbaum

variable [Encodable α]
variable (H)
variable {t : Tableau α}

open Classical
open Encodable

def lindenbaum_next (φ : Formula α) (t : Tableau α) : Tableau α := if Tableau.Consistent H (insert φ t.1, t.2) then (insert φ t.1, t.2) else (t.1, insert φ t.2)

def lindenbaum_next_indexed [Encodable α] (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some φ => (lindenbaum_next_indexed t i).lindenbaum_next H φ
    | none => lindenbaum_next_indexed t i
local notation:max t"[" i "]" => lindenbaum_next_indexed H t i

def lindenbaum_maximal (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_maximal H t

variable {H}

omit [Encodable α] in
lemma next_parametericConsistent (consistent : Tableau.Consistent H t) (φ : Formula α) : Tableau.Consistent H (t.lindenbaum_next H φ) := by
  simp [lindenbaum_next];
  split;
  . simpa;
  . have := consistent_either consistent φ;
    simp_all only [false_or];

omit [H.IncludeEFQ] in
@[simp]
lemma lindenbaum_next_indexed_zero {t : Tableau α} : (t.lindenbaum_next_indexed H 0) = t := by simp [lindenbaum_next_indexed]

lemma lindenbaum_next_indexed_parametricConsistent_succ {i : ℕ} : Tableau.Consistent H t[i] → Tableau.Consistent H t[i + 1] := by
  simp [lindenbaum_next_indexed];
  split;
  . intro h; apply next_parametericConsistent; assumption;
  . tauto;

omit [H.IncludeEFQ] in
lemma mem_lindenbaum_next_indexed (t) (φ : Formula α) : φ ∈ t[(encode φ) + 1].1 ∨ φ ∈ t[(encode φ) + 1].2 := by
  simp [lindenbaum_next_indexed, lindenbaum_next];
  split;
  . left; tauto;
  . right; tauto;

lemma lindenbaum_next_indexed_parametricConsistent (consistent : Tableau.Consistent H t) (i : ℕ) : Tableau.Consistent H t[i] := by
  induction i with
  | zero => simpa;
  | succ i ih => apply lindenbaum_next_indexed_parametricConsistent_succ; assumption;

variable {m n : ℕ}

omit [H.IncludeEFQ] in
lemma lindenbaum_next_indexed_subset₁_of_lt (h : m ≤ n) : t[m].1 ⊆ t[n].1 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_next_indexed, lindenbaum_next];
    split;
    . split <;> tauto;
    . tauto;

omit [H.IncludeEFQ] in
lemma lindenbaum_next_indexed_subset₂_of_lt (h : m ≤ n) : t[m].2 ⊆ t[n].2 := by
  induction h with
  | refl => simp;
  | step h ih =>
    simp [lindenbaum_next_indexed, lindenbaum_next];
    split;
    . split <;> tauto;
    . tauto;

lemma exists_parametricConsistent_saturated_tableau (hCon : Tableau.Consistent H t) : ∃ u, t ⊆ u ∧ (Tableau.Consistent H u) ∧ (Saturated u) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?saturated⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case saturated =>
    intro φ;
    cases mem_lindenbaum_next_indexed t φ with
    | inl h => left; simp [lindenbaum_maximal]; use (encode φ + 1);
    | inr h => right; simp [lindenbaum_maximal]; use (encode φ + 1);
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

structure SaturatedConsistentTableau (H : Hilbert α) where
  tableau : Tableau α
  saturated : Saturated tableau
  consistent : Tableau.Consistent H tableau

alias SCT := SaturatedConsistentTableau

namespace SaturatedConsistentTableau

variable {t₀ : Tableau α} {φ ψ : Formula α}

lemma lindenbaum [H.IncludeEFQ] [Encodable α] (hCon : Tableau.Consistent H t₀) : ∃ (t : SaturatedConsistentTableau H), t₀ ⊆ t.tableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [H.Consistent] [H.IncludeEFQ] [Encodable α] : Nonempty (SCT H) := ⟨lindenbaum Tableau.self_consistent |>.choose⟩

variable {t : SCT H}

@[simp] lemma disjoint : Disjoint t.tableau.1 t.tableau.2 := t.tableau.disjoint_of_consistent t.consistent

lemma not_mem₁_iff_mem₂ : φ ∉ t.tableau.1 ↔ φ ∈ t.tableau.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma not_mem₂_iff_mem₁ : φ ∉ t.tableau.2 ↔ φ ∈ t.tableau.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

variable {t t₁ t₂ : SCT H}

lemma saturated_duality: t₁.tableau.1 = t₂.tableau.1 ↔ t₁.tableau.2 = t₂.tableau.2 := Tableau.saturated_duality t₁.consistent t₂.consistent t₁.saturated t₂.saturated

lemma equality_of₁ (e₁ : t₁.tableau.1 = t₂.tableau.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (saturated_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.tableau, t₁.saturated, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.tableau, t₂.saturated, t₂.consistent⟩ := by simp [e];
    _  = t₂                                        := by rfl;

lemma equality_of₂ (e₂ : t₁.tableau.2 = t₂.tableau.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ φ ∈ Γ, φ ∈ t.tableau.1) (h : H ⊢! ⋀Γ ➝ ψ) : ψ ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp₁ (hp₁ : φ ∈ t.tableau.1) (h : H ⊢! φ ➝ ψ) : ψ ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hq₂;
  have : H ⊬ φ ➝ ψ := by simpa using t.consistent (Γ := [φ]) (Δ := [ψ]) (by simpa) (by simpa);
  contradiction;

@[simp]
lemma mem₁_verum : ⊤ ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : H ⊬ ⋀[] ➝ ⋁[⊤] := t.consistent (by simp) (by simpa);
  have : H ⊢! ⋀[] ➝ ⋁[⊤] := by simp;
  contradiction;

@[simp]
lemma not_mem₁_falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : H ⊬ ⋀[⊥] ➝ ⋁[] := t.consistent (by simpa) (by simp);
  have : H ⊢! ⋀[⊥] ➝ ⋁[] := by simp;
  contradiction;

@[simp]
lemma iff_mem₁_and : φ ⋏ ψ ∈ t.tableau.1 ↔ φ ∈ t.tableau.1 ∧ ψ ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp₁ h (by simp)
  . rintro ⟨hp, hq⟩;
    apply not_mem₂_iff_mem₁.mp;
    by_contra hC;
    have : H ⊢! ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := by simp;
    have : H ⊬ ⋀[φ, ψ] ➝ ⋁[φ ⋏ ψ] := t.consistent (by simp_all) (by simp_all);
    contradiction;

lemma iff_mem₁_conj {Γ : List (Formula α)} : ⋀Γ ∈ t.tableau.1 ↔ ∀ φ ∈ Γ, φ ∈ t.tableau.1 := by
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

@[simp]
lemma iff_mem₁_or : φ ⋎ ψ ∈ t.tableau.1 ↔ φ ∈ t.tableau.1 ∨ ψ ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; push_neg at hC;
    have : φ ∈ t.tableau.2 := not_mem₁_iff_mem₂.mp hC.1;
    have : ψ ∈ t.tableau.2 := not_mem₁_iff_mem₂.mp hC.2;
    have : H ⊢! ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := by simp;
    have : H ⊬ ⋀[φ ⋎ ψ] ➝ ⋁[φ, ψ] := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp₁ h or₁!
    | inr h => exact mdp₁ h or₂!

lemma not_mem₁_neg_of_mem₁ [DecidableEq α] : φ ∈ t.tableau.1 → ∼φ ∉ t.tableau.1 := by
  intro hp;
  by_contra hnp;
  have := iff_mem₁_and.mpr ⟨hp, hnp⟩;
  have : ⊥ ∈ t.tableau.1 := mdp₁ (ψ := ⊥) this (by simp);
  have : ⊥ ∉ t.tableau.1 := not_mem₁_falsum
  contradiction;

lemma mem₂_neg_of_mem₁ [DecidableEq α] : φ ∈ t.tableau.1 → ∼φ ∈ t.tableau.2 := by
  intro h;
  exact not_mem₁_iff_mem₂ (φ := ∼φ) (t := t) |>.mp $ not_mem₁_neg_of_mem₁ h;

lemma mem₁_of_provable : H ⊢! φ → φ ∈ t.tableau.1 := by
  intro h;
  exact mdp₁ mem₁_verum $ imply₁'! h;

lemma mdp₁_mem [DecidableEq α] (hp : φ ∈ t.tableau.1) (h : φ ➝ ψ ∈ t.tableau.1) : ψ ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : H ⊬ (φ ⋏ (φ ➝ ψ)) ➝ ψ := t.consistent (Γ := [φ, φ ➝ ψ]) (Δ := [ψ]) (by aesop) (by simpa);
  have : H ⊢! (φ ⋏ (φ ➝ ψ)) ➝ ψ := mdp_in!
  contradiction;

end SaturatedConsistentTableau

import Logic.Propositional.Superintuitionistic.Deduction

set_option autoImplicit false
universe u v

namespace LO.Propositional.Superintuitionistic

open System FiniteContext
open Formula

variable {α : Type u} [DecidableEq α] [Inhabited α]
variable {Λ : DeductionParameter α} [Λ.IncludeEFQ]

def Tableau (α : Type u) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

def ParametricConsistent (Λ : DeductionParameter α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ t.1) → (∀ p ∈ Δ, p ∈ t.2) → Λ ⊬! ⋀Γ ⟶ ⋁Δ
notation "(" Λ ")-Consistent" => ParametricConsistent Λ

variable {p q: Formula α} {T U : Theory α}

lemma iff_ParametricConsistent_insert₁ : (Λ)-Consistent ((insert p T), U) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → (∀ p ∈ Δ, p ∈ U) → Λ ⊬! p ⋏ ⋀Γ ⟶ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : Λ ⊬! ⋀(p :: Γ) ⟶ ⋁Δ := h (by simp; intro q hq; right; exact hΓ q hq;) hΔ;
    have : Λ ⊢! ⋀(p :: Γ) ⟶ ⋁Δ := iff_imply_left_cons_conj'!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all only [Set.mem_insert_iff];
    have : Λ ⊬! p ⋏ ⋀(Γ.remove p) ⟶ ⋁Δ := h (by
      intro q hq;
      have := by simpa using hΓ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    ) hΔ;
    by_contra hC;
    have : Λ ⊢! p ⋏ ⋀(Γ.remove p) ⟶ ⋁Δ := imp_trans''! and_comm! $ imply_left_remove_conj! (p := p) hC;
    contradiction;

lemma iff_not_ParametricConsistent_insert₁ : ¬(Λ)-Consistent ((insert p T), U) ↔ ∃ Γ Δ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ (∀ p ∈ Δ, p ∈ U) ∧ Λ ⊢! p ⋏ ⋀Γ ⟶ ⋁Δ := by
  constructor;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₁.mpr;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₁.mp;

lemma iff_ParametricConsistent_insert₂ : (Λ)-Consistent (T, (insert p U)) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → (∀ p ∈ Δ, p ∈ U) → Λ ⊬! ⋀Γ ⟶ p ⋎ ⋁Δ := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : Λ ⊬! ⋀Γ ⟶ ⋁(p :: Δ) := h hΓ (by simp; intro q hq; right; exact hΔ q hq);
    have : Λ ⊢! ⋀Γ ⟶ ⋁(p :: Δ) := implyRight_cons_disj!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all;
    have : Λ ⊬! ⋀Γ ⟶ p ⋎ ⋁(Δ.remove p) := h hΓ (by
      intro q hq;
      have := by simpa using hΔ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have : Λ ⊢! ⋀Γ ⟶ p ⋎ ⋁(Δ.remove p) := imp_trans''! hC $ forthback_disj_remove;
    contradiction;


lemma iff_not_ParametricConsistent_insert₂ : ¬(Λ)-Consistent (T, (insert p U)) ↔ ∃ Γ Δ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ (∀ p ∈ Δ, p ∈ U) ∧ Λ ⊢! ⋀Γ ⟶ p ⋎ ⋁Δ := by
  constructor;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₂.mp;

section Consistent

variable {t} (hCon : (Λ)-Consistent t)

lemma consistent_either (p : Formula α) : (Λ)-Consistent ((insert p t.1), t.2) ∨ (Λ)-Consistent (t.1, (insert p t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_ParametricConsistent_insert₁.mp hC₁;
  replace h₁ := imply_left_and_comm'! h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_ParametricConsistent_insert₂.mp hC₂;

  have : Λ ⊢! ⋀(Γ₁ ++ Γ₂) ⟶ ⋁(Δ₁ ++ Δ₂) := imp_trans''! (and₁'! iff_concat_conj!) $ imp_trans''! (cut! h₁ h₂) (and₂'! iff_concact_disj!);
  have : Λ ⊬! ⋀(Γ₁ ++ Γ₂) ⟶ ⋁(Δ₁ ++ Δ₂) := hCon (by simp; rintro q (hq₁ | hq₂); exact hΓ₁ q hq₁; exact hΓ₂ q hq₂) (by simp; rintro q (hq₁ | hq₂); exact hΔ₁ q hq₁; exact hΔ₂ q hq₂);
  contradiction;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [ParametricConsistent] at hCon;
  have : Λ ⊬! ⋀[p] ⟶ ⋁[p] := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : Λ ⊢! ⋀[p] ⟶ ⋁[p] := by simp;
  contradiction;

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.1) (h : Λ ⊢! ⋀Γ ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! ⋀Γ ⟶ ⋁[q] := by simpa;
  have : Λ ⊬! ⋀Γ ⟶ ⋁[q] := hCon (by aesop) (by aesop);
  contradiction;

end Consistent


abbrev Saturated (t : Tableau α) := ∀ p : Formula α, p ∈ t.1 ∨ p ∈ t.2

section Saturated

variable {t : Tableau α}
variable (hCon : (Λ)-Consistent t := by assumption) (hMat : Saturated t := by assumption)

lemma mem₂_of_not_mem₁ : p ∉ t.1 → p ∈ t.2 := by
  intro h;
  cases (hMat p) with
  | inl h' => exact absurd h' h;
  | inr _ => assumption;

lemma mem₁_of_not_mem₂ : p ∉ t.2 → p ∈ t.1 := by
  intro h;
  cases (hMat p) with
  | inl _ => assumption;
  | inr h' => exact absurd h' h;

lemma not_mem₁_iff_mem₂ : p ∉ t.1 ↔ p ∈ t.2 := by
  constructor;
  . apply mem₂_of_not_mem₁ hMat;
  . apply Set.disjoint_right.mp $ disjoint_of_consistent hCon;

lemma not_mem₂_iff_mem₁ : p ∉ t.2 ↔ p ∈ t.1 := by
  constructor;
  . apply mem₁_of_not_mem₂ hMat;
  . apply Set.disjoint_left.mp $ disjoint_of_consistent hCon;

lemma saturated_duality
  {t₁ t₂ : Tableau α}
  (ct₁ : (Λ)-Consistent t₁) (ct₂ : (Λ)-Consistent t₂)
  (st₁ : Saturated t₁) (st₂ : Saturated t₂)
  : t₁.1 = t₂.1 ↔ t₁.2 = t₂.2 := by
  constructor;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      apply not_mem₁_iff_mem₂ ct₂ |>.mp; rw [←h];
      apply not_mem₁_iff_mem₂ ct₁ |>.mpr hp;
    . intro p hp;
      apply not_mem₁_iff_mem₂ ct₁ |>.mp; rw [h];
      apply not_mem₁_iff_mem₂ ct₂ |>.mpr hp;
  . intro h;
    apply Set.eq_of_subset_of_subset;
    . intro p hp;
      apply not_mem₂_iff_mem₁ ct₂ |>.mp; rw [←h];
      apply not_mem₂_iff_mem₁ ct₁ |>.mpr hp;
    . intro p hp;
      apply not_mem₂_iff_mem₁ ct₁ |>.mp; rw [h];
      apply not_mem₂_iff_mem₁ ct₂ |>.mpr hp;

end Saturated

variable [Inhabited α]

lemma self_ParametricConsistent [h : System.Consistent Λ] : (Λ)-Consistent (Ax(Λ), ∅) := by
  intro Γ Δ hΓ hΔ;
  replace hΔ : Δ = [] := List.nil_iff.mpr hΔ;
  obtain ⟨q, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : Λ ⊢! q := by
    subst hΔ;
    simp at hC;
    exact imp_trans''! hC efq! ⨀ (by
      apply iff_provable_list_conj.mpr;
      exact λ _ hp => ⟨Deduction.eaxm $ hΓ _ hp⟩;
    );
  contradiction;

section lindenbaum

variable [Encodable α]
variable (Λ)
variable {t : Tableau α}

open Classical
open Encodable

def lindenbaum_next (p : Formula α) (t : Tableau α) : Tableau α := if (Λ)-Consistent (insert p t.1, t.2) then (insert p t.1, t.2) else (t.1, insert p t.2)

def lindenbaum_next_indexed (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some p => (lindenbaum_next_indexed t i).lindenbaum_next Λ p
    | none => lindenbaum_next_indexed t i
local notation:max t"[" i "]" => lindenbaum_next_indexed Λ t i

def lindenbaum_maximal (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_maximal Λ t

variable {Λ}

lemma next_parametericConsistent (consistent : (Λ)-Consistent t) (p : Formula α) : (Λ)-Consistent (t.lindenbaum_next Λ p) := by
  simp [lindenbaum_next];
  split;
  . simpa;
  . have := consistent_either consistent p;
    simp_all only [false_or];

@[simp]
lemma lindenbaum_next_indexed_zero {t : Tableau α} : (t.lindenbaum_next_indexed Λ 0) = t := by simp [lindenbaum_next_indexed]

lemma lindenbaum_next_indexed_parametricConsistent_succ {i : ℕ} : (Λ)-Consistent t[i] → (Λ)-Consistent t[i + 1] := by
  simp [lindenbaum_next_indexed];
  split;
  . intro h; apply next_parametericConsistent; assumption;
  . tauto;

lemma mem_lindenbaum_next_indexed (t) (p : Formula α) : p ∈ t[(encode p) + 1].1 ∨ p ∈ t[(encode p) + 1].2 := by
  simp [lindenbaum_next_indexed, lindenbaum_next];
  split;
  . left; tauto;
  . right; tauto;

lemma lindenbaum_next_indexed_parametricConsistent (consistent : (Λ)-Consistent t) (i : ℕ) : (Λ)-Consistent t[i] := by
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

lemma exists_parametricConsistent_saturated_tableau (hCon : (Λ)-Consistent t) : ∃ u, t ⊆ u ∧ ((Λ)-Consistent u) ∧ (Saturated u) := by
  use t∞;
  refine ⟨?subset, ?consistent, ?saturated⟩;
  case subset => constructor <;> apply Set.subset_iUnion_of_subset 0 (by simp);
  case saturated =>
    intro p;
    cases mem_lindenbaum_next_indexed t p with
    | inl h => left; simp [lindenbaum_maximal]; use (encode p + 1);
    | inr h => right; simp [lindenbaum_maximal]; use (encode p + 1);
  case consistent =>
    intro Γ Δ hΓ hΔ;
    simp_all [lindenbaum_maximal];
    obtain ⟨m, hΓ⟩ : ∃ m, ∀ p ∈ Γ, p ∈ t[m].1 := by
      induction Γ with
      | nil => simp;
      | cons p Γ ih =>
        simp_all;
        obtain ⟨i, hi⟩ := hΓ.1;
        obtain ⟨m, hm⟩ := ih;
        use (i + m);
        constructor;
        . exact lindenbaum_next_indexed_subset₁_of_lt (by simp) hi;
        . intro q hq;
          exact lindenbaum_next_indexed_subset₁_of_lt (by simp) $ hm q hq;
    obtain ⟨n, hΔ⟩ : ∃ n, ∀ p ∈ Δ, p ∈ t[n].2 := by
      induction Δ with
      | nil => simp;
      | cons p Δ ih =>
        simp_all;
        obtain ⟨i, hi⟩ := hΔ.1;
        obtain ⟨n, hn⟩ := ih;
        use (i + n);
        constructor;
        . exact lindenbaum_next_indexed_subset₂_of_lt (by simp) hi;
        . intro q hq;
          exact lindenbaum_next_indexed_subset₂_of_lt (by simp) $ hn q hq;
    rcases (lt_trichotomy m n) with hm | hmn | hn;
    . exact lindenbaum_next_indexed_parametricConsistent hCon n (by intro p hp; exact lindenbaum_next_indexed_subset₁_of_lt hm.le $ hΓ p hp) hΔ;
    . subst hmn;
      exact lindenbaum_next_indexed_parametricConsistent hCon m hΓ hΔ;
    . exact lindenbaum_next_indexed_parametricConsistent hCon m hΓ (by intro p hp; exact lindenbaum_next_indexed_subset₂_of_lt hn.le $ hΔ p hp);

protected alias lindenbaum := exists_parametricConsistent_saturated_tableau

end lindenbaum

end Tableau

variable [Encodable α]

open Tableau

structure SaturatedConsistentTableau (Λ : DeductionParameter α) where
  tableau : Tableau α
  saturated : Saturated tableau
  consistent : (Λ)-Consistent tableau

alias SCT := SaturatedConsistentTableau

namespace SaturatedConsistentTableau

variable {t₀ : Tableau α} {p q : Formula α}

lemma lindenbaum (hCon : (Λ)-Consistent t₀) : ∃ (t : SaturatedConsistentTableau Λ), t₀ ⊆ t.tableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

instance [System.Consistent Λ] : Nonempty (SCT Λ) := ⟨lindenbaum Tableau.self_ParametricConsistent |>.choose⟩

variable {t : SCT Λ}

@[simp] lemma disjoint : Disjoint t.tableau.1 t.tableau.2 := t.tableau.disjoint_of_consistent t.consistent

lemma not_mem₁_iff_mem₂ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma not_mem₂_iff_mem₁ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

variable {t t₁ t₂ : SCT Λ}

lemma saturated_duality: t₁.tableau.1 = t₂.tableau.1 ↔ t₁.tableau.2 = t₂.tableau.2 := Tableau.saturated_duality t₁.consistent t₂.consistent t₁.saturated t₂.saturated

lemma equality_of₁ (e₁ : t₁.tableau.1 = t₂.tableau.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (saturated_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.tableau, t₁.saturated, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.tableau, t₂.saturated, t₂.consistent⟩ := by simp [e];
    _  = t₂                                        := by rfl;

lemma equality_of₂ (e₂ : t₁.tableau.2 = t₂.tableau.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.tableau.1) (h : Λ ⊢! ⋀Γ ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp₁ (hp₁ : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hq₂;
  have : Λ ⊬! p ⟶ q := by simpa using t.consistent (Γ := [p]) (Δ := [q]) (by simpa) (by simpa);
  contradiction;

@[simp]
lemma mem₁_verum : ⊤ ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : Λ ⊬! ⋀[] ⟶ ⋁[⊤] := t.consistent (by simp) (by simpa);
  have : Λ ⊢! ⋀[] ⟶ ⋁[⊤] := by simp;
  contradiction;

@[simp]
lemma not_mem₁_falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! ⋀[⊥] ⟶ ⋁[] := t.consistent (by simpa) (by simp);
  have : Λ ⊢! ⋀[⊥] ⟶ ⋁[] := by simp;
  contradiction;

@[simp]
lemma iff_mem₁_and : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp₁ h (by simp)
  . rintro ⟨hp, hq⟩;
    apply not_mem₂_iff_mem₁.mp;
    by_contra hC;
    have : Λ ⊢! ⋀[p, q] ⟶ ⋁[p ⋏ q] := by simp;
    have : Λ ⊬! ⋀[p, q] ⟶ ⋁[p ⋏ q] := t.consistent (by simp_all) (by simp_all);
    contradiction;

lemma iff_mem₁_conj {Γ : List (Formula α)} : ⋀Γ ∈ t.tableau.1 ↔ ∀ p ∈ Γ, p ∈ t.tableau.1 := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle p => simp;
  | hcons p Γ Γ_nil ih =>
    simp only [(List.conj₂_cons_nonempty Γ_nil), List.mem_cons];
    constructor;
    . rintro h p (rfl | hp);
      . exact iff_mem₁_and.mp h |>.1;
      . exact ih.mp (iff_mem₁_and.mp h |>.2) _ hp;
    . intro h;
      apply iff_mem₁_and.mpr;
      simp_all;

@[simp]
lemma iff_mem₁_or : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; push_neg at hC;
    have : p ∈ t.tableau.2 := not_mem₁_iff_mem₂.mp hC.1;
    have : q ∈ t.tableau.2 := not_mem₁_iff_mem₂.mp hC.2;
    have : Λ ⊢! ⋀[p ⋎ q] ⟶ ⋁[p, q] := by simp;
    have : Λ ⊬! ⋀[p ⋎ q] ⟶ ⋁[p, q] := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp₁ h or₁!
    | inr h => exact mdp₁ h or₂!

lemma not_mem₁_neg_of_mem₁ : p ∈ t.tableau.1 → ~p ∉ t.tableau.1 := by
  intro hp;
  by_contra hnp;
  have := iff_mem₁_and.mpr ⟨hp, hnp⟩;
  have : ⊥ ∈ t.tableau.1 := mdp₁ (q := ⊥) this (by simp);
  have : ⊥ ∉ t.tableau.1 := not_mem₁_falsum
  contradiction;

lemma mem₂_neg_of_mem₁ : p ∈ t.tableau.1 → ~p ∈ t.tableau.2 := by
  intro h;
  exact not_mem₁_iff_mem₂ (p := ~p) (t := t) |>.mp $ not_mem₁_neg_of_mem₁ h;

lemma mem₁_of_provable : Λ ⊢! p → p ∈ t.tableau.1 := by
  intro h;
  exact mdp₁ mem₁_verum $ dhyp! h;

lemma mdp₁_mem (hp : p ∈ t.tableau.1) (h : p ⟶ q ∈ t.tableau.1) : q ∈ t.tableau.1 := by
  apply not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : Λ ⊬! (p ⋏ (p ⟶ q)) ⟶ q := t.consistent (Γ := [p, p ⟶ q]) (Δ := [q]) (by aesop) (by simpa);
  have : Λ ⊢! (p ⋏ (p ⟶ q)) ⟶ q := mdp_in!
  contradiction;

end SaturatedConsistentTableau

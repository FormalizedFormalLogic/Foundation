import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Soundness


namespace LO.Propositional.Superintuitionistic

open System FiniteContext
open Formula Formula.Kripke

variable [DecidableEq α] [Inhabited α]
variable {𝓓 : DeductionParameter α} [𝓓.IncludeEFQ]

def Tableau (α) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

@[simp] lemma equality_def {t₁ t₂ : Tableau α} : t₁ = t₂ ↔ t₁.1 = t₂.1 ∧ t₁.2 = t₂.2 := by
  constructor;
  . intro h; cases h; simp;
  . rintro ⟨h₁, h₂⟩; cases t₁; cases t₂; simp_all;

def ParametricConsistent (𝓓 : DeductionParameter α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ t.1) → (∀ p ∈ Δ, p ∈ t.2) → 𝓓 ⊬! Γ.conj' ⟶ Δ.disj'
notation "(" 𝓓 ")-Consistent" => ParametricConsistent 𝓓


lemma iff_ParametricConsistent_insert₁ : (𝓓)-Consistent ((insert p T), U) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → (∀ p ∈ Δ, p ∈ U) → 𝓓 ⊬! p ⋏ Γ.conj' ⟶ Δ.disj' := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : 𝓓 ⊬! (p :: Γ).conj' ⟶ Δ.disj' := h (by simp; intro q hq; right; exact hΓ q hq;) hΔ;
    have : 𝓓 ⊢! (p :: Γ).conj' ⟶ Δ.disj' := implyLeft_cons_conj'!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all only [Set.mem_insert_iff];
    have : 𝓓 ⊬! p ⋏ (Γ.remove p).conj' ⟶ Δ.disj' := h (by
      intro q hq;
      have := by simpa using hΓ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    ) hΔ;
    by_contra hC;
    have : 𝓓 ⊢! p ⋏ (Γ.remove p).conj' ⟶ Δ.disj' := imp_trans''! and_comm! $ imply_left_remove_conj'! (p := p) hC;
    contradiction;

lemma iff_not_ParametricConsistent_insert₁ : ¬(𝓓)-Consistent ((insert p T), U) ↔ ∃ Γ Δ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ (∀ p ∈ Δ, p ∈ U) ∧ 𝓓 ⊢! p ⋏ Γ.conj' ⟶ Δ.disj' := by
  constructor;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₁.mpr;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₁.mp;

lemma iff_ParametricConsistent_insert₂ : (𝓓)-Consistent (T, (insert p U)) ↔ ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ T) → (∀ p ∈ Δ, p ∈ U) → 𝓓 ⊬! Γ.conj' ⟶ p ⋎ Δ.disj' := by
  constructor;
  . intro h Γ Δ hΓ hΔ;
    by_contra hC;
    have : 𝓓 ⊬! Γ.conj' ⟶ (p :: Δ).disj' := h hΓ (by simp; intro q hq; right; exact hΔ q hq);
    have : 𝓓 ⊢! Γ.conj' ⟶ (p :: Δ).disj' := implyRight_cons_disj'!.mpr hC;
    contradiction;
  . intro h Γ Δ hΓ hΔ;
    simp_all;
    have : 𝓓 ⊬! Γ.conj' ⟶ p ⋎ (Δ.remove p).disj' := h hΓ (by
      intro q hq;
      have := by simpa using hΔ q $ List.mem_of_mem_remove hq;
      cases this with
      | inl h => simpa [h] using List.mem_remove_iff.mp hq;
      | inr h => assumption;
    );
    by_contra hC;
    have : 𝓓 ⊢! Γ.conj' ⟶ p ⋎ (Δ.remove p).disj' := imp_trans''! hC $ forthback_disj'_remove;
    contradiction;


lemma iff_not_ParametricConsistent_insert₂ : ¬(𝓓)-Consistent (T, (insert p U)) ↔ ∃ Γ Δ : List (Formula α), (∀ p ∈ Γ, p ∈ T) ∧ (∀ p ∈ Δ, p ∈ U) ∧ 𝓓 ⊢! Γ.conj' ⟶ p ⋎ Δ.disj' := by
  constructor;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₂.mpr;
  . contrapose; push_neg; apply iff_ParametricConsistent_insert₂.mp;

section Consistent

variable (hCon : (𝓓)-Consistent t)

lemma consistent_either (p : Formula α) : (𝓓)-Consistent ((insert p t.1), t.2) ∨ (𝓓)-Consistent (t.1, (insert p t.2)) := by
  by_contra hC;
  push_neg at hC;
  have ⟨hC₁, hC₂⟩ := hC;

  obtain ⟨Γ₁, Δ₁, hΓ₁, hΔ₁, h₁⟩ := iff_not_ParametricConsistent_insert₁.mp hC₁;
  replace h₁ := imply_left_and_comm'! h₁;

  obtain ⟨Γ₂, Δ₂, hΓ₂, hΔ₂, h₂⟩ := iff_not_ParametricConsistent_insert₂.mp hC₂;

  have : 𝓓 ⊢! (Γ₁ ++ Γ₂).conj' ⟶ (Δ₁ ++ Δ₂).disj' := imp_trans''! (and₁'! iff_concat_conj!) $ imp_trans''! (cut! h₁ h₂) (and₂'! iff_concact_disj!);
  have : 𝓓 ⊬! (Γ₁ ++ Γ₂).conj' ⟶ (Δ₁ ++ Δ₂).disj' := hCon (by simp; rintro q (hq₁ | hq₂); exact hΓ₁ q hq₁; exact hΓ₂ q hq₂) (by simp; rintro q (hq₁ | hq₂); exact hΔ₁ q hq₁; exact hΔ₂ q hq₂);
  contradiction;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₁, hp₂, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [ParametricConsistent] at hCon;
  have : 𝓓 ⊬! [p].conj' ⟶ [p].disj' := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : 𝓓 ⊢! [p].conj' ⟶ [p].disj' := by simp;
  contradiction;

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.1) (h : 𝓓 ⊢! Γ.conj' ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : 𝓓 ⊢! Γ.conj' ⟶ [q].disj' := by simpa;
  have : 𝓓 ⊬! Γ.conj' ⟶ [q].disj' := hCon (by aesop) (by aesop);
  contradiction;

end Consistent


abbrev Saturated (t : Tableau α) := ∀ p : Formula α, p ∈ t.1 ∨ p ∈ t.2

section Saturated

variable (hCon : (𝓓)-Consistent t := by assumption) (hMat : Saturated t := by assumption)

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
  (ct₁ : (𝓓)-Consistent t₁) (ct₂ : (𝓓)-Consistent t₂)
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

lemma self_ParametricConsistent [h : System.Consistent 𝓓] : (𝓓)-Consistent (Ax(𝓓), ∅) := by
  intro Γ Δ hΓ hΔ;
  replace hΔ : Δ = [] := List.nil_iff.mpr hΔ;
  obtain ⟨q, hq⟩ := h.exists_unprovable;
  by_contra hC;
  have : 𝓓 ⊢! q := by
    subst hΔ;
    simp [List.disj'_nil] at hC;
    exact imp_trans''! hC efq! ⨀ (by
      apply iff_provable_list_conj.mpr;
      exact λ _ hp => ⟨Deduction.eaxm $ hΓ _ hp⟩;
    );
  contradiction;

section lindenbaum

variable [Encodable α]
variable (𝓓)
variable {t : Tableau α}

open Classical
open Encodable

def lindenbaum_next (p : Formula α) (t : Tableau α) : Tableau α := if (𝓓)-Consistent (insert p t.1, t.2) then (insert p t.1, t.2) else (t.1, insert p t.2)

def lindenbaum_next_indexed (t : Tableau α) : ℕ → Tableau α
  | 0 => t
  | i + 1 =>
    match (decode i) with
    | some p => (lindenbaum_next_indexed t i).lindenbaum_next 𝓓 p
    | none => lindenbaum_next_indexed t i
local notation:max t"[" i "]" => lindenbaum_next_indexed 𝓓 t i

def lindenbaum_maximal (t : Tableau α) : Tableau α := (⋃ i, t[i].1, ⋃ i, t[i].2)
local notation:max t"∞" => lindenbaum_maximal 𝓓 t

variable {𝓓}

lemma next_parametericConsistent (consistent : (𝓓)-Consistent t) (p : Formula α) : (𝓓)-Consistent (t.lindenbaum_next 𝓓 p) := by
  simp [lindenbaum_next];
  split;
  . simpa;
  . have := consistent_either consistent p;
    simp_all only [false_or];

@[simp]
lemma lindenbaum_next_indexed_zero {t : Tableau α} : (t.lindenbaum_next_indexed 𝓓 0) = t := by simp [lindenbaum_next_indexed]

lemma lindenbaum_next_indexed_parametricConsistent_succ {i : ℕ} : (𝓓)-Consistent t[i] → (𝓓)-Consistent t[i + 1] := by
  simp [lindenbaum_next_indexed];
  split;
  . intro h; apply next_parametericConsistent; assumption;
  . tauto;

lemma mem_lindenbaum_next_indexed (t) (p : Formula α) : p ∈ t[(encode p) + 1].1 ∨ p ∈ t[(encode p) + 1].2 := by
  simp [lindenbaum_next_indexed, lindenbaum_next];
  split;
  . left; tauto;
  . right; tauto;

lemma lindenbaum_next_indexed_parametricConsistent (consistent : (𝓓)-Consistent t) (i : ℕ) : (𝓓)-Consistent t[i] := by
  induction i with
  | zero => simpa;
  | succ i ih => apply lindenbaum_next_indexed_parametricConsistent_succ; assumption;

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

lemma exists_parametricConsistent_saturated_tableau (hCon : (𝓓)-Consistent t) : ∃ u, t ⊆ u ∧ ((𝓓)-Consistent u) ∧ (Saturated u) := by
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

structure SaturatedConsistentTableau (𝓓 : DeductionParameter α) where
  tableau : Tableau α
  saturated : Saturated tableau
  consistent : (𝓓)-Consistent tableau

alias SCT := SaturatedConsistentTableau

namespace SaturatedConsistentTableau

lemma lindenbaum (hCon : (𝓓)-Consistent t₀) : ∃ (t : SaturatedConsistentTableau 𝓓), t₀ ⊆ t.tableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

noncomputable instance [System.Consistent 𝓓] : Inhabited (SCT 𝓓) := ⟨lindenbaum Tableau.self_ParametricConsistent |>.choose⟩

variable (t : SCT 𝓓)

@[simp] lemma disjoint : Disjoint t.tableau.1 t.tableau.2 := t.tableau.disjoint_of_consistent t.consistent

lemma not_mem₁_iff_mem₂ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma not_mem₂_iff_mem₁ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

variable {t t₁ t₂ : SCT 𝓓}

lemma saturated_duality: t₁.tableau.1 = t₂.tableau.1 ↔ t₁.tableau.2 = t₂.tableau.2 := Tableau.saturated_duality t₁.consistent t₂.consistent t₁.saturated t₂.saturated

lemma equality_of₁ (e₁ : t₁.tableau.1 = t₂.tableau.1) : t₁ = t₂ := by
  have e := Tableau.equality_def.mpr ⟨e₁, (saturated_duality.mp e₁)⟩;
  calc
    t₁ = ⟨t₁.tableau, t₁.saturated, t₁.consistent⟩ := by rfl;
    _  = ⟨t₂.tableau, t₂.saturated, t₂.consistent⟩ := by simp [e];
    _  = t₂                                        := by rfl;

lemma equality_of₂ (e₂ : t₁.tableau.2 = t₂.tableau.2) : t₁ = t₂ := equality_of₁ $ saturated_duality.mpr e₂

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.tableau.1) (h : 𝓓 ⊢! Γ.conj' ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp₁ (hp : p ∈ t.tableau.1) (h : 𝓓 ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  exact t.not_mem₂_iff_mem₁.mp $ not_mem₂ (by simpa) (show 𝓓 ⊢! List.conj' [p] ⟶ q by simpa;)

@[simp]
lemma mem₁_verum : ⊤ ∈ t.tableau.1 := by
  apply t.not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : 𝓓 ⊬! [].conj' ⟶ [⊤].disj' := t.consistent (by simp) (by simpa);
  have : 𝓓 ⊢! [].conj' ⟶ [⊤].disj' := by simp;
  contradiction;

@[simp]
lemma not_mem₁_falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : 𝓓 ⊬! [⊥].conj' ⟶ [].disj' := t.consistent (by simpa) (by simp);
  have : 𝓓 ⊢! [⊥].conj' ⟶ [].disj' := by simp;
  contradiction;

@[simp]
lemma iff_mem₁_and : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp₁ h (by simp)
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    have : 𝓓 ⊢! [p, q].conj' ⟶ [p ⋏ q].disj' := by simp;
    have : 𝓓 ⊬! [p, q].conj' ⟶ [p ⋏ q].disj' := t.consistent (by aesop) (by simpa using t.not_mem₁_iff_mem₂.mp hC);
    contradiction;

@[simp]
lemma iff_mem₁_or : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.1;
    have : q ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.2;
    have : 𝓓 ⊢! [p ⋎ q].conj' ⟶ [p, q].disj' := by simp;
    have : 𝓓 ⊬! [p ⋎ q].conj' ⟶ [p, q].disj' := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp₁ h or₁!
    | inr h => exact mdp₁ h or₂!

lemma mem₁_of_provable : 𝓓 ⊢! p → p ∈ t.tableau.1 := by
  intro h;
  exact mdp₁ mem₁_verum $ dhyp! h;

end SaturatedConsistentTableau


namespace Kripke

open SaturatedConsistentTableau

def CanonicalFrame (𝓓 : DeductionParameter α) [Inhabited (SCT 𝓓)] : Frame' α where
  World := SCT 𝓓
  Rel := λ t₁ t₂ => t₁.tableau.1 ⊆ t₂.tableau.1
  Rel_antisymm := by
    intro x y hxy hyx;
    exact equality_of₁ $ Set.Subset.antisymm hxy hyx;
  Rel_trans := by intro x y z; apply Set.Subset.trans;

def CanonicalModel (𝓓 : DeductionParameter α) [Inhabited (SCT 𝓓)] : Model α where
  Frame := CanonicalFrame 𝓓
  Valuation t a := (atom a) ∈ t.tableau.1
  hereditary := by aesop;


namespace CanonicalModel

variable [Inhabited (SCT 𝓓)]

@[reducible]
instance : Semantics (Formula α) (CanonicalModel 𝓓).World := instKripkeSemanticsFormulaWorld (CanonicalModel 𝓓)

@[simp] lemma frame_def {t₁ t₂ : SCT 𝓓} : (CanonicalModel 𝓓).Rel t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {t : SCT 𝓓} {a : α} : (CanonicalModel 𝓓).Valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end CanonicalModel

section

variable [Inhabited (SCT 𝓓)]

variable {t : SCT 𝓓}

private lemma truthlemma.himp
  {t : (CanonicalModel 𝓓).World}
  (ihp : ∀ {t : (CanonicalModel 𝓓).World}, t ⊧ p ↔ p ∈ t.tableau.1)
  (ihq : ∀ {t : (CanonicalModel 𝓓).World}, t ⊧ q ↔ q ∈ t.tableau.1)
  : t ⊧ p ⟶ q ↔ p ⟶ q ∈ t.tableau.1 := by
  constructor;
  . contrapose;
    simp_all;
    intro h;
    replace h := t.not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (𝓓 := 𝓓) (t₀ := (insert p t.tableau.1, {q})) $ by
      simp only [Tableau.ParametricConsistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ r, r ∈ Γ.remove p → r ∈ t.tableau.1 := by
        intro r hr;
        have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
        have := by simpa using hΓ r hr₁;
        simp_all;
      by_contra hC;
      have : 𝓓 ⊢! (Γ.remove p).conj' ⟶ (p ⟶ q) := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj'! hC) (by
        apply deduct'!;
        apply deduct!;
        have : [p, p ⟶ Δ.disj'] ⊢[𝓓]! p := by_axm!;
        have : [p, p ⟶ Δ.disj'] ⊢[𝓓]! Δ.disj' := by_axm! ⨀ this;
        exact disj_allsame'! (by simpa using hΔ) this;
      )
      have : 𝓓 ⊬! (Γ.remove p).conj' ⟶ (p ⟶ q) := by simpa only [List.disj'_singleton] using (t.consistent hΓ (show ∀ r ∈ [p ⟶ q], r ∈ t.tableau.2 by simp_all));
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    existsi t';
    constructor;
    . simp_all only [Set.singleton_subset_iff];
    . constructor;
      . assumption;
      . apply t'.not_mem₁_iff_mem₂.mpr;
        simp_all only [Set.singleton_subset_iff];
  . simp [Satisfies.imp_def];
    intro h t' htt' hp;
    replace hp := ihp.mp hp;
    have hpq := htt' h;
    apply ihq.mpr;
    apply t'.not_mem₂_iff_mem₁.mp;
    exact not_mem₂
      (by simp_all)
      (show 𝓓 ⊢! [p, p ⟶ q].conj' ⟶ q by
        simp;
        apply and_imply_iff_imply_imply'!.mpr;
        apply deduct'!;
        apply deduct!;
        exact by_axm! ⨀ (by_axm! (p := p));
      );

private lemma truthlemma.hneg
  {t : (CanonicalModel 𝓓).World}
  (ihp : ∀ {t : (CanonicalModel 𝓓).World}, t ⊧ p ↔ p ∈ t.tableau.1)
  : t ⊧ ~p ↔ ~p ∈ t.tableau.1 := by
  constructor;
  . contrapose; simp_all;
    intro h;
    replace h := t.not_mem₁_iff_mem₂.mp h;
    obtain ⟨t', ⟨h, _⟩⟩ := lindenbaum (𝓓 := 𝓓) (t₀ := (insert p t.tableau.1, ∅)) $ by
      simp only [Tableau.ParametricConsistent];
      intro Γ Δ hΓ hΔ;
      replace hΓ : ∀ q, q ∈ Γ.remove p → q ∈ t.tableau.1 := by
        intro q hq;
        have ⟨hq₁, hq₂⟩ := List.mem_remove_iff.mp hq;
        have := by simpa using hΓ q hq₁;
        simp_all;
      replace hΔ : Δ = [] := List.nil_iff.mpr hΔ; subst hΔ;
      by_contra hC; simp at hC;
      have : 𝓓 ⊢! (Γ.remove p).conj' ⟶ ~p := imp_trans''! (and_imply_iff_imply_imply'!.mp $ imply_left_remove_conj'! hC) (and₂'! neg_equiv!);
      have : 𝓓 ⊬! (Γ.remove p).conj' ⟶ ~p := by simpa only [List.disj'_singleton] using t.consistent (Δ := [~p]) hΓ (by simpa);
      contradiction;
    have ⟨_, _⟩ := Set.insert_subset_iff.mp h;
    existsi t';
    constructor;
    . simp_all only [Set.singleton_subset_iff];
    . assumption;
  . simp;
    intro ht t' htt';
    apply ihp.not.mpr;
    by_contra hC;
    have : 𝓓 ⊬! p ⋏ ~p ⟶ ⊥ := by simpa using t'.consistent (Γ := [p, ~p]) (Δ := []) (by aesop) (by simp);
    have : 𝓓 ⊢! p ⋏ ~p ⟶ ⊥ := intro_bot_of_and!;
    contradiction;

lemma truthlemma {t : (CanonicalModel 𝓓).World} : t ⊧ p ↔ p ∈ t.tableau.1 := by
  induction p using rec' generalizing t with
  | himp p q ihp ihq => exact truthlemma.himp ihp ihq
  | hneg p ihp => exact truthlemma.hneg ihp;
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma deducible_of_validOnCanonicelModel : (CanonicalModel 𝓓) ⊧ p ↔ 𝓓 ⊢! p := by
  constructor;
  . contrapose;
    intro h;
    have : (𝓓)-Consistent (∅, {p}) := by
      simp only [Tableau.ParametricConsistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
      rintro Γ Δ hΓ hΔ;
      by_contra hC;
      replace hΓ : Γ = [] := List.nil_iff.mpr hΓ;
      subst hΓ;
      have : 𝓓 ⊢! p := disj_allsame'! hΔ (hC ⨀ verum!);
      contradiction;
    obtain ⟨t', ht'⟩ := lindenbaum this;
    simp [ValidOnModel.iff_models, ValidOnModel]
    existsi t';
    apply truthlemma.not.mpr;
    apply t'.not_mem₁_iff_mem₂.mpr;
    simp_all;
  . intro h t;
    suffices p ∈ t.tableau.1 by exact truthlemma.mpr this;
    exact mem₁_of_provable h;

end

class Canonical (𝓓 : DeductionParameter α) [Inhabited (SCT 𝓓)] where
  realize : (CanonicalFrame 𝓓) ⊧* Ax(𝓓)

lemma complete! [System.Consistent 𝓓] [Canonical 𝓓] : (𝔽(Ax(𝓓)) : FrameClass' α) ⊧ p → 𝓓 ⊢! p := by
  intro h;
  apply deducible_of_validOnCanonicelModel.mp;
  exact h Canonical.realize _ _;

instance instComplete [System.Consistent 𝓓] [Canonical 𝓓] : Complete 𝓓 𝔽(Ax(𝓓)) := ⟨complete!⟩

instance canonical_of_definability [Inhabited (SCT 𝓓)] (definability : Definability Ax(𝓓) P) (h : P (CanonicalFrame 𝓓)) : Canonical 𝓓 where
  realize := definability.defines _ |>.mpr h;

instance : Canonical (𝐈𝐧𝐭 : DeductionParameter α) := canonical_of_definability AxiomSet.EFQ.definability trivial

instance intComplete : Complete (𝐈𝐧𝐭 : DeductionParameter α) 𝔽(Ax(𝐈𝐧𝐭)) := instComplete

end Kripke

end LO.Propositional.Superintuitionistic

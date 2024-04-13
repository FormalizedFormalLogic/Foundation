import Logic.Modal.Normal.Deduction
import Logic.Modal.Normal.Semantics

/-!
  Some definitions and lemmata to prove Kripke completeness.
-/

namespace LO.Modal.Normal

open Hilbert
open Finset Set
open Formula Theory

attribute [simp] Finset.subset_union_right Finset.subset_union_left
attribute [simp] Set.Subset.rfl Set.insert_subset_iff

variable {α β : Type u} [Inhabited α] [DecidableEq β] [Inhabited β]

section

variable (Λ : AxiomSet β) (Γ : Theory β)

def Theory.Maximal := ∀ p, (p ∈ Γ) ∨ (~p ∈ Γ)

-- def WeakCompleteness := ∀ (p : Formula β), (⊧ᴹ[(𝔽(Λ) : FrameClass α)] p) → (∅ ⊢ᴹ[Λ]! p)

def KripkeCompleteness (𝔽 : FrameClass α) := ∀ (Γ : Theory β) (p : Formula β), (Γ ⊨ᴹ[𝔽] p) → (Γ ⊢ᴹ[Λ]! p)

end

variable {Λ : AxiomSet β}
variable {Γ : Theory β} (hConsisΓ : Consistent Λ Γ)

@[simp]
lemma inconsistent_insert_falsum : Inconsistent Λ (insert ⊥ Γ) := Hilbert.inconsistent_insert_falsum

lemma consistent_iff_undeducible_falsum : Consistent Λ Γ ↔ (Γ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_iff_undeducible_falsum

@[simp]
lemma consistent_undeducible_falsum : Γ ⊬ᴹ[Λ]! ⊥ := consistent_iff_undeducible_falsum.mp hConsisΓ

lemma consistent_subset_undeducible_falsum (Δ) (hΔ : Δ ⊆ Γ) : (Δ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_subset_undeducible_falsum hConsisΓ hΔ

lemma consistent_no_falsum : ⊥ ∉ Γ := Hilbert.consistent_no_falsum hConsisΓ

lemma consistent_no_falsum_subset (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := Hilbert.consistent_no_falsum_subset hConsisΓ hΔ

lemma consistent_neither_undeducible (p) : (Γ ⊬ᴹ[Λ]! p) ∨ (Γ ⊬ᴹ[Λ]! ~p) := Hilbert.consistent_neither_undeducible hConsisΓ p

lemma consistent_of_subset (h : Γ₁ ⊆ Γ₂) : (Consistent Λ Γ₂) → (Consistent Λ Γ₁) := Hilbert.consistent_of_subset h

lemma consistent_insert {Γ : Theory β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_of_subset (by simp)

lemma consistent_empty (hConsisΛ : Theory.Consistent Λ Λ) : Theory.Consistent Λ ∅ := consistent_of_subset (by simp) hConsisΛ

lemma inconsistent_insert (h : Inconsistent Λ (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢ᴹ[Λ]! ⊥)) := Hilbert.inconsistent_insert h

lemma consistent_iff_insert_neg  : (Consistent Λ (insert (~p) Γ)) ↔ (Γ ⊬ᴹ[Λ]! p)  := Hilbert.consistent_iff_insert_neg

lemma consistent_either (hConsisΓ : Consistent Λ Γ) : ∀ p, (Consistent Λ (insert p Γ)) ∨ (Consistent Λ (insert (~p) Γ)) := Hilbert.consistent_either hConsisΓ

-- TODO: move to Deduction
lemma inconsistent_union {Γ₁ Γ₂} (h : Inconsistent Λ (Γ₁ ∪ Γ₂)) : (∃ (Δ₁ Δ₂ : Context β), (↑Δ₁ ⊆ Γ₁) ∧ (↑Δ₂ ⊆ Γ₂) ∧ (Δ₁ ∪ Δ₂ ⊢ᴹ[Λ]! ⊥)) := by
  have ⟨⟨Δ, hΔ⟩, hd⟩ := h.some.compact;
  obtain ⟨Δ₁, Δ₂, hΔeq, hΔ₁, hΔ₂⟩ := Finset.subset_union_elim hΔ;
  replace ⟨hΔ₂, _⟩ := Set.subset_diff.mp hΔ₂;
  subst hΔeq;
  simp at hd;
  use Δ₁, Δ₂;
  exact ⟨hΔ₁, hΔ₂, ⟨hd⟩⟩;

-- TODO: move
@[simp]
lemma Theory.Inconsistent_iff : Inconsistent Λ Γ ↔ ¬(Consistent Λ Γ) := by
  simp [Theory.Inconsistent, Theory.Consistent, Deduction.Inconsistent, Deduction.Consistent, Deduction.Undeducible, Deduction.Deducible]

lemma frameclass_unsatisfiable_insert_neg {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊭ᴹ[𝔽] p) ↔ (Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by
  constructor;
  . intro hCon;
    simp [FrameClassConsequence, FrameConsequence] at hCon;
    simp [FrameClassSatisfiable, FrameSatisfiable];
    have ⟨F, hF, V, w, ⟨h₁, h₂⟩⟩ := hCon;
    existsi F, hF, V, w;
    exact ⟨h₂, h₁⟩;
  . intro hSat hCon;
    simp [FrameClassConsequence, FrameConsequence] at hCon;
    simp [FrameClassSatisfiable, FrameSatisfiable] at hSat;
    have ⟨F, hF, V, w, ⟨h₁, h₂⟩⟩ := hSat;
    exact h₁ $ hCon F hF V w h₂;

lemma frameclass_satisfiable_insert_neg {𝔽 : FrameClass α} {Γ : Theory β} : (Γ ⊨ᴹ[𝔽] p) ↔ ¬(Theory.FrameClassSatisfiable 𝔽 (insert (~p) Γ)) := by simpa using frameclass_unsatisfiable_insert_neg.not

lemma completeness_def {𝔽 : FrameClass α} : (KripkeCompleteness Λ 𝔽) ↔ (∀ Γ, Consistent Λ Γ → FrameClassSatisfiable 𝔽 Γ) := by
  constructor;
  . contrapose;
    simp [KripkeCompleteness];
    intro Δ h₁ h₂;
    existsi Δ, ⊥;
    constructor;
    . intro F hF V w h;
      simp [FrameClassSatisfiable, FrameSatisfiable] at h₂;
      have ⟨p, ⟨hp₁, hp₂⟩⟩ := h₂ F hF V w;
      have := h p hp₁;
      contradiction;
    . simpa [Theory.Consistent, Theory.Inconsistent, Deduction.Consistent, Deduction.Undeducible, Deduction.Deducible] using h₁;
  . contrapose;
    simp [KripkeCompleteness];
    intro Δ p h₁ h₂;
    existsi (insert (~p) Δ);
    constructor;
    . apply consistent_iff_insert_neg.mpr;
      simpa using h₂;
    . apply frameclass_satisfiable_insert_neg.mp;
      exact h₁;


def Theory.MaximalConsistent (Λ) (Γ : Theory β) := Theory.Consistent Λ Γ ∧ Maximal Γ

section MaximalConsistent

variable (hMCΓ : MaximalConsistent Λ Γ)

lemma maximal_consistent_include_axiomset : Λ ⊆ Γ := by
  intro p hp;
  by_contra hC;
  have h₁ : {~p} ⊬ᴹ[Λ]! ⊥ := consistent_subset_undeducible_falsum hMCΓ.1 {~p} (by have := hMCΓ.2 p; aesop)
  have h₂ : {~p} ⊢ᴹ[Λ]! ⊥ := by simpa using dtl'! $ dni'! (show ∅ ⊢ᴹ[Λ]! p by exact Deducible.maxm! hp);
  contradiction;

lemma maximal_consistent_iff_membership_deducible : (p ∈ Γ) ↔ (Γ ⊢ᴹ[Λ]! p) := by
  constructor;
  . intro h; exact (Hilbert.axm! h)
  . intro h;
    suffices ~p ∉ Γ by have := hMCΓ.2 p; aesop;
    by_contra hC;
    have h₂ : Γ ⊢ᴹ[Λ]! ~p := Hilbert.axm! hC;
    exact consistent_subset_undeducible_falsum hMCΓ.1 Γ (by simp) (h₂ ⨀ h);

lemma maximal_consistent_iff_not_membership_undeducible : (p ∉ Γ) ↔ (Γ ⊬ᴹ[Λ]! p) := by
  simpa using (maximal_consistent_iff_membership_deducible hMCΓ).not;

lemma maximal_consistent_modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Γ) → (p ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq;
  have dp  := (maximal_consistent_iff_membership_deducible hMCΓ).mp hp;
  have dpq := (maximal_consistent_iff_membership_deducible hMCΓ).mp hpq;
  exact (maximal_consistent_iff_membership_deducible hMCΓ).mpr $ dp ⨀ dpq;

lemma maximal_consistent_neg_membership_iff : (~p ∈ Γ) ↔ (p ∉ Γ) := by
  constructor;
  . intros;
    by_contra hC;
    have hp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hnp : ({p, ~p}) ⊢ᴹ[Λ]! ~p := axm! (by simp);
    apply consistent_subset_undeducible_falsum hMCΓ.1 {p, ~p} (by aesop;) (hnp ⨀ hp);
  . have := hMCΓ.2 p; aesop;

lemma maximal_consistent_imp_membership_iff : (p ⟶ q ∈ Γ) ↔ (p ∉ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . simp [or_iff_not_imp_left];
    intros;
    apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
    have hp : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hpq : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p ⟶ q := axm! (by simp);
    have : ({p, p ⟶ q}) ⊢ᴹ[Λ]! q := hpq ⨀ hp
    exact weakening! (by aesop) this;
  . intros h;
    cases h;
    case inl h =>
      have := (maximal_consistent_neg_membership_iff hMCΓ).mpr h;
      have d₁ : Γ ⊢ᴹ[Λ]! (~p ⟶ (p ⟶ q)) := by
        have dp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
        have dnp : ({p, ~p}) ⊢ᴹ[Λ]! (~p) := axm! (by simp);
        have h₂ : ({p, ~p}) ⊢ᴹ[Λ]! q := efq'! $ dnp ⨀ dp;
        have h₃ : ∅ ⊢ᴹ[Λ]! ~p ⟶ (p ⟶ q) := dtr'! (by simpa using dtr'! h₂);
        exact weakening! (by simp) h₃;
      have d₂ : Γ ⊢ᴹ[Λ]! ~p := axm! (by simpa)
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact d₁ ⨀ d₂;
    case inr h =>
      have d₁ : Γ ⊢ᴹ[Λ]! (q ⟶ (p ⟶ q)) := imply₁!;
      have d₂ : Γ ⊢ᴹ[Λ]! q := axm! h;
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact d₁ ⨀ d₂;

lemma maximal_consistent_imp_membership_iff' : (p ⟶ q ∈ Γ) ↔ ((p ∈ Γ) → (q ∈ Γ)) := by
  constructor;
  . intro hpq hp;
    have := (maximal_consistent_imp_membership_iff hMCΓ).mp hpq;
    aesop;
  . intro hp;
    apply (maximal_consistent_imp_membership_iff hMCΓ).mpr;
    simp [or_iff_not_imp_left];
    aesop;

lemma maximal_consistent_and_membership_iff : (p ⋏ q ∈ Γ) ↔ (p ∈ Γ) ∧ (q ∈ Γ) := by
  constructor;
  . intros h;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    constructor;
    . exact conj₁'! h;
    . exact conj₂'! h;
  . rintro ⟨hp, hq⟩;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    exact conj₃'! hp hq;

lemma maximal_consistent_or_membership_iff : (p ⋎ q ∈ Γ) ↔ (p ∈ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . intros h;
    by_contra hC; simp [not_or] at hC;
    have : Γ ⊢ᴹ[Λ]! ⊥ := disj₃'!
      (show Γ ⊢ᴹ[Λ]! (p ⟶ ⊥) by exact axm! (by apply maximal_consistent_neg_membership_iff hMCΓ |>.mpr; aesop;))
      (show Γ ⊢ᴹ[Λ]! (q ⟶ ⊥) by exact axm! (by apply maximal_consistent_neg_membership_iff hMCΓ |>.mpr; aesop;))
      (show Γ ⊢ᴹ[Λ]! (p ⋎ q) by exact axm! h);
    exact consistent_undeducible_falsum hMCΓ.1 this;
  . intro h;
    simp_all only [(maximal_consistent_iff_membership_deducible hMCΓ)];
    cases h;
    case inl h => exact disj₁'! h;
    case inr h => exact disj₂'! h;

end MaximalConsistent

structure MaximalConsistentTheory (Λ : AxiomSet β) where
  theory : Theory β
  mc : MaximalConsistent Λ theory

namespace MaximalConsistentTheory

variable (Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ)
variable (hK : 𝐊 ⊆ Λ)

@[simp] def membership (p : Formula β) (Ω : MaximalConsistentTheory Λ) := p ∈ Ω.theory
instance : Membership (Formula β) (MaximalConsistentTheory Λ) := ⟨membership⟩

@[simp] def subset := Ω₁.theory ⊆ Ω₂.theory
instance : HasSubset (MaximalConsistentTheory Λ) := ⟨subset⟩

instance : CoeSort (MaximalConsistentTheory Λ) (Theory β) := ⟨λ Ω => Ω.theory⟩

lemma equality_def {Ω₁ Ω₂ : MaximalConsistentTheory Λ} : Ω₁ = Ω₂ ↔ Ω₁.theory = Ω₂.theory := by
  constructor;
  . intro h; cases h; rfl;
  . intro h; cases Ω₁; cases Ω₂; simp_all;

lemma intro_equality {Ω₁ Ω₂ : MaximalConsistentTheory Λ} {h : ∀ p, p ∈ Ω₁ → p ∈ Ω₂} : Ω₁ = Ω₂ := by
  have h₁₂ : Ω₁ ⊆ Ω₂ := by intro p hp; exact h p hp;
  have h₂₁ : Ω₂ ⊆ Ω₁ := by
    intro p;
    contrapose;
    intro hp;
    apply maximal_consistent_neg_membership_iff Ω₂.mc |>.mp;
    apply h;
    apply maximal_consistent_neg_membership_iff Ω₁.mc |>.mpr hp;
  simpa [equality_def] using Set.eq_of_subset_of_subset h₁₂ h₂₁

lemma consitent : Consistent Λ Ω.theory := Ω.mc.1

lemma maximal : Maximal Ω.theory := Ω.mc.2

variable {Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ}

lemma modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Ω) → (p ∈ Ω) → (q ∈ Ω) := by
  apply maximal_consistent_modus_ponens' (Ω.mc);

lemma membership_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (p ∈ Ω) ↔ (Ω.theory ⊢ᴹ[Λ]! p) := by
  apply maximal_consistent_iff_membership_deducible (Ω.mc);

lemma iff_congr : (Ω.theory ⊢ᴹ[Λ]! (p ⟷ q)) → ((p ∈ Ω) ↔ (q ∈ Ω)) := by
  intro hpq;
  simp only [LogicalConnective.iff] at hpq;
  constructor;
  . intro hp;
    exact membership_iff.mpr $ (conj₁'! hpq) ⨀ (membership_iff.mp hp)
  . intro hq;
    exact membership_iff.mpr $ (conj₂'! hpq) ⨀ (membership_iff.mp hq)

lemma dn_membership_iff : (p ∈ Ω) ↔ (~~p ∈ Ω) := iff_congr $ equiv_dn!

lemma neg_membership_iff : (~p ∈ Ω) ↔ (p ∉ Ω) := maximal_consistent_neg_membership_iff (Ω.mc)

lemma imp_membership_iff' : (p ⟶ q ∈ Ω) ↔ ((p ∈ Ω) → (q ∈ Ω)) := maximal_consistent_imp_membership_iff' (Ω.mc)

lemma and_membership_iff : (p ⋏ q ∈ Ω) ↔ (p ∈ Ω) ∧ (q ∈ Ω) := maximal_consistent_and_membership_iff (Ω.mc)

lemma or_membership_iff : (p ⋎ q ∈ Ω) ↔ (p ∈ Ω) ∨ (q ∈ Ω) := maximal_consistent_or_membership_iff (Ω.mc)

lemma neg_imp (h : q ∈ Ω₂ → p ∈ Ω₁) : (~p ∈ Ω₁) → (~q ∈ Ω₂) := by
  contrapose;
  intro hq;
  replace hq := dn_membership_iff.mpr $ neg_membership_iff.mpr hq;
  apply neg_membership_iff.mp;
  apply dn_membership_iff.mp;
  apply h;
  assumption;

lemma not_membership_imp (h : q ∈ Ω₂ → p ∈ Ω₁) : (p ∉ Ω₁) → (q ∉ Ω₂) := by
  intro hp;
  apply neg_membership_iff.mp;
  replace hp := neg_membership_iff.mpr hp;
  revert hp;
  exact neg_imp h;

lemma neg_iff (h : p ∈ Ω₁ ↔ q ∈ Ω₂) : (~p ∈ Ω₁) ↔ (~q ∈ Ω₂) := by
  constructor;
  . apply neg_imp; exact h.mpr;
  . apply neg_imp; exact h.mp;

lemma box_dn_iff {p : Formula β} : (□p ∈ Ω) ↔ (□(~~p) ∈ Ω) := by
  have := Deduction.ofKSubset hK;
  constructor;
  . intro h;
    apply membership_iff.mpr;
    have : Ω.theory ⊢ᴹ[Λ]! □(p ⟶ ~~p) := weakening! (show ∅ ⊆ Ω.theory by simp) $ necessitation! $ dni!;
    have : Ω.theory ⊢ᴹ[Λ]! □p := membership_iff.mp h;
    have : Ω.theory ⊢ᴹ[Λ]! □~~p := axiomK'! (by assumption) (by assumption);
    assumption;
  . intro h;
    apply membership_iff.mpr;
    have : Ω.theory ⊢ᴹ[Λ]! □(~~p ⟶ p) := weakening! (show ∅ ⊆ Ω.theory by simp) $ necessitation! $ dne!;
    have : Ω.theory ⊢ᴹ[Λ]! □~~p := membership_iff.mp h;
    have : Ω.theory ⊢ᴹ[Λ]! □p := axiomK'! (by assumption) (by assumption);
    assumption;

lemma dia_dn_iff {p : Formula β} : (◇p ∈ Ω) ↔ (◇(~(~p)) ∈ Ω) := by
  apply neg_iff;
  apply box_dn_iff;
  assumption;

lemma box_dual {p : Formula β} : (□p ∈ Ω) ↔ (~(◇(~p)) ∈ Ω) := by
  constructor;
  . intro h;
    apply dn_membership_iff.mp;
    exact box_dn_iff hK |>.mp h;
  . intro h;
    exact box_dn_iff hK |>.mpr $ dn_membership_iff.mpr h

lemma multibox_dual {n : ℕ} {p : Formula β} : (□[n]p ∈ Ω) ↔ (~(◇[n](~p)) ∈ Ω) := by
  have := Deduction.ofKSubset hK;
  have := Deduction.instBoxedNecessitation hK;

  have d : Ω.theory ⊢ᴹ[Λ]! □[n]p ⟷ ~(◇[n](~p)) := multibox_duality!

  constructor;
  . intro h;
    have : Ω.theory ⊢ᴹ[Λ]! ~(◇[n](~p)) := (iff_mp'! d) ⨀ (membership_iff.mp h);
    apply membership_iff.mpr;
    assumption;
  . intro h;
    have : Ω.theory ⊢ᴹ[Λ]! □[n]p := (iff_mpr'! d) ⨀ (membership_iff.mp h);
    apply membership_iff.mpr;
    assumption;

lemma dia_dual {p : Formula β} : (◇p ∈ Ω) ↔ (~(□(~p)) ∈ Ω) := by simp [ModalDuality.dia_to_box];

lemma multidia_dual {n : ℕ} {p : Formula β} : (◇[n]p ∈ Ω) ↔ (~(□[n](~p)) ∈ Ω) := by
  have := Deduction.ofKSubset hK;
  have := Deduction.instBoxedNecessitation hK;

  have d : Ω.theory ⊢ᴹ[Λ]! ◇[n]p ⟷ ~(□[n](~p)) := multidia_duality!

  constructor;
  . intro h;
    have : Ω.theory ⊢ᴹ[Λ]! ~(□[n](~p)) := (iff_mp'! d) ⨀ membership_iff.mp h;
    apply membership_iff.mpr;
    assumption;
  . intro h;
    have : Ω.theory ⊢ᴹ[Λ]! ◇[n]p := (iff_mpr'! d) ⨀ membership_iff.mp h;
    apply membership_iff.mpr;
    assumption;

lemma multidia_prepost {n : ℕ} {p : Formula β} : (◇◇[n]p ∈ Ω) ↔ (◇[n](◇p) ∈ Ω) := by simp only [Dia.multidia_prepost];

lemma mutlidia_prepost' {n : ℕ} {p : Formula β} : (◇[(n + 1)]p ∈ Ω) ↔ (◇[n](◇p) ∈ Ω) := by simp [Dia.multidia_prepost];

@[simp]
lemma no_falsum : ⊥ ∉ Ω := consistent_no_falsum Ω.consitent

@[simp]
lemma neither_mem : ¬((p ∈ Ω) ∧ (~p ∈ Ω)) := by
  by_contra hC;
  exact Ω.no_falsum $ Ω.modus_ponens' hC.2 hC.1;

lemma multibox_multidia {Ω₁ Ω₂ : MaximalConsistentTheory Λ} : (∀ {p : Formula β}, (□[n]p ∈ Ω₁ → p ∈ Ω₂)) ↔ (∀ {p : Formula β}, (p ∈ Ω₂ → ◇[n]p ∈ Ω₁)) := by
  constructor;
  . intro H p;
    contrapose;
    intro h;
    apply neg_membership_iff.mp;
    apply H;
    apply dn_membership_iff.symm |>.mp;
    apply (neg_iff $ multidia_dual hK).mp;
    exact neg_membership_iff.mpr h;
  . intro H p;
    contrapose;
    intro h;
    apply neg_membership_iff.mp;
    apply (neg_iff $ multibox_dual hK).symm.mp;
    apply dn_membership_iff.symm |>.mpr;
    apply H;
    apply neg_membership_iff.mpr;
    assumption

lemma context_conj_membership_iff {Δ : Context β} : ⋀Δ ∈ Ω ↔ (∀ p ∈ Δ, p ∈ Ω) := by
  simp only [membership_iff];
  constructor;
  . intro h p hp;
    exact finset_conj_iff!.mp h p hp;
  . intro h;
    exact finset_conj_iff!.mpr h;

lemma context_box_conj_membership_iff {Δ : Context β} : □(⋀Δ) ∈ Ω ↔ (∀ p ∈ Δ, □p ∈ Ω) := by
  have := Deduction.ofKSubset hK;
  have := Deduction.instBoxedNecessitation hK;

  simp only [membership_iff];
  constructor;
  . intro h p hp;
    exact box_finset_conj_iff!.mp h p hp;
  . intro h;
    exact box_finset_conj_iff!.mpr h;

lemma context_box_conj_membership_iff' {Δ : Context β} : □(⋀Δ) ∈ Ω ↔ (∀ p ∈ (□Δ : Context β), p ∈ Ω) := by
  simp [Context.box, Finset.box, List.multibox];
  apply context_box_conj_membership_iff hK;

lemma context_multibox_conj_membership_iff {Δ : Context β} {n : ℕ} : □[n](⋀Δ) ∈ Ω ↔ (∀ p ∈ Δ, □[n]p ∈ Ω) := by
  have := Deduction.ofKSubset hK;
  have := Deduction.instBoxedNecessitation hK;

  simp only [membership_iff];
  constructor;
  . intro h p hp;
    exact multibox_finset_conj_iff!.mp h p hp;
  . intro h;
    exact multibox_finset_conj_iff!.mpr h;

lemma context_multibox_conj_membership_iff' {Δ : Context β} : □[n](⋀Δ) ∈ Ω ↔ (∀ p ∈ (□[n]Δ : Context β), p ∈ Ω):= by
  simp [Context.multibox, Finset.multibox, List.multibox];
  apply context_multibox_conj_membership_iff hK;

end MaximalConsistentTheory

section Lindenbaum

lemma exists_maximal_consistent_theory' :
  ∃ m ∈ {Γ | Theory.Consistent Λ Γ}, Γ ⊆ m ∧ ∀ a ∈ {Γ | Theory.Consistent Λ Γ}, m ⊆ a → a = m
  := zorn_subset_nonempty { Γ : Theory β | Consistent Λ Γ } (by
    intro c hc chain hnc;
    existsi (⋃₀ c);
    simp;
    constructor;
    . by_contra hC;
      replace hC : ⋃₀ c ⊢ᴹ[Λ]! ⊥ := by simpa [Theory.Consistent, Theory.Inconsistent, Deduction.not_consistent] using hC;
      rcases hC.compact with ⟨s, hs, s_consis⟩;
      rcases Set.subset_mem_chain_of_finite c hnc chain (s := s) (Finset.finite_toSet s) hs with ⟨U, hUc, hsU⟩
      exact (consistent_of_subset hsU (by apply hc; simpa)) s_consis;
    . intro s a;
      exact Set.subset_sUnion_of_mem a;
  ) Γ hConsisΓ

/--
  a.k.a. Lindenbaum Lemma
-/
lemma exists_maximal_consistent_theory : ∃ (Ω : MaximalConsistentTheory Λ), (Γ ⊆ Ω.theory) := by
  have ⟨Ω, ⟨h₁, ⟨h₂, h₃⟩⟩⟩ := exists_maximal_consistent_theory' hConsisΓ;
  existsi ⟨Ω, h₁, (by
    intro p;
    cases (consistent_either h₁ p) with
    | inl h => have := h₃ (insert p Ω) h (by simp); left; simpa;
    | inr h => have := h₃ (insert (~p) Ω) h (by simp); right; simpa;
  )⟩;
  exact h₂;

end Lindenbaum

variable (hK : 𝐊 ⊆ Λ)

open MaximalConsistentTheory

lemma mct_mem_box_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (□p ∈ Ω) ↔ (∀ (Ω' : MaximalConsistentTheory Λ), (□⁻¹Ω ⊆ Ω'.theory) → (p ∈ Ω')) := by
  have := Deduction.instBoxedNecessitation hK;
  constructor;
  . aesop;
  . contrapose;
    intro hC;
    have := (maximal_consistent_iff_not_membership_undeducible Ω.mc).mp hC;
    have := consistent_iff_insert_neg.mpr $ not_imp_not.mpr preboxed_necessitation! this;
    have ⟨Ω', hΩ'⟩ := exists_maximal_consistent_theory this;
    simp;
    existsi Ω';
    constructor;
    . aesop;
    . exact neg_membership_iff.mp (by aesop);

def CanonicalModel (Λ : AxiomSet β) : Model (MaximalConsistentTheory Λ) β where
  frame (Ω₁ Ω₂) := (□⁻¹Ω₁) ⊆ Ω₂.theory
  val (Ω a) := (atom a) ∈ Ω

namespace CanonicalModel

variable {Λ : AxiomSet β} (hK : 𝐊 ⊆ Λ) {Ω Ω₁ Ω₂ : MaximalConsistentTheory Λ}

lemma frame_def: (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (∀ {p : Formula β}, □p ∈ Ω₁ → p ∈ Ω₂) := by rfl

lemma frame_def': (CanonicalModel Λ).frame Ω₁ Ω₂ ↔ (◇Ω₂ ⊆ Ω₁.theory) := by
  have := Deduction.instBoxedNecessitation hK;
  have := Deduction.ofKSubset hK;

  simp only [frame_def];
  constructor;
  . intro h p hp;
    have ⟨q, hq₁, hq₂⟩ := Set.dia_mem_iff.mp hp;
    rw [←hq₂, ModalDuality.dia_to_box];
    apply (Ω₁.neg_membership_iff).mpr;
    by_contra hC;
    have : ~q ∈ Ω₂ := by aesop;
    exact Ω₂.neither_mem ⟨hq₁, (by simpa)⟩;
  . intro h p;
    contrapose;
    intro hnp;
    have : ◇(~p) ∈ Ω₁ := by simpa using h $ dia_mem_intro $ neg_membership_iff.mpr hnp;
    have : ~(□p) ∈ Ω₁ := by
      suffices h : Ω₁.theory ⊢ᴹ[Λ]! ((◇~p) ⟷ ~(□p)) by exact MaximalConsistentTheory.iff_congr h |>.mp this;
      apply equiv_dianeg_negbox!;
    have := neg_membership_iff.mp this;
    aesop;

lemma multiframe_box : (CanonicalModel Λ).frame[n] Ω₁ Ω₂ ↔ (∀ {p : Formula β}, (□[n]p ∈ Ω₁ → p ∈ Ω₂)) := by
  have := Deduction.instBoxedNecessitation hK;
  have := Deduction.ofKSubset hK;

  constructor;
  . induction n generalizing Ω₁ Ω₂ with
    | zero => intro h; subst h; simp;
    | succ n ih =>
      simp;
      intro Ω₃ h₁₃ h₃₂ p h;
      exact ih h₃₂ $ h₁₃ h;
  . induction n generalizing Ω₁ Ω₂ with
    | zero => intro h; apply intro_equality; simpa;
    | succ n ih =>
      intro h;
      obtain ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory (show Consistent Λ (□⁻¹Ω₁ ∪ ◇[n]Ω₂) by
        by_contra hInc;
        obtain ⟨Δ₁, Δ₂, hΔ₁, hΔ₂, hUd⟩ := inconsistent_union (by simpa only [Theory.Inconsistent_iff] using hInc);

        have h₁ : □⋀Δ₁ ∈ Ω₁ := by -- TODO: refactor
          apply context_box_conj_membership_iff' hK |>.mpr;
          have : □(↑Δ₁ : Theory β) ⊆ Ω₁ := subset_prebox_iff_box_subset hΔ₁;
          simp only [←Context.box_coe_eq] at this;
          intro p hp;
          exact this hp;

        have h₂ : ⋀(◇⁻¹[n]Δ₂) ∈ Ω₂ := by -- TODO: refactor
          apply context_conj_membership_iff.mpr;
          have : ◇⁻¹[n](↑Δ₂ : Theory β) ⊆ Ω₂.theory := subset_multidia_iff_premulitidia_subset hΔ₂;
          simp only [←Context.premultidia_coe_eq] at this;
          intro p hp;
          exact this hp;

        have e : (◇[n](◇⁻¹[n]Δ₂) : Context β) = Δ₂ := by simpa using premultidia_multidia_eq_of_subset_multidia hΔ₂;

        have : ⋀(◇⁻¹[n]Δ₂) ∉ Ω₂ := by
          have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₁ ∪ Δ₂) := by simpa [NegDefinition.neg] using finset_dt!.mp (by simpa using hUd);
          have : ∅ ⊢ᴹ[Λ]! ~⋀(Δ₁ ∪ Δ₂) ⟶ ~(⋀Δ₁ ⋏ ⋀Δ₂) := contra₀'! $ iff_mpr'! $ finset_union_conj!;
          have : ∅ ⊢ᴹ[Λ]! ~(⋀Δ₁ ⋏ ⋀Δ₂) := (by assumption) ⨀ (by assumption);
          have : ∅ ⊢ᴹ[Λ]! ◇[n](⋀◇⁻¹[n]Δ₂) ⟶ ⋀(◇[n](◇⁻¹[n]Δ₂)) := by apply distribute_multidia_finset_conj!;
          have : ∅ ⊢ᴹ[Λ]! ◇[n](⋀◇⁻¹[n]Δ₂) ⟶ ⋀Δ₂ := by simpa only [e];
          have : ∅ ⊢ᴹ[Λ]! ~⋀Δ₂ ⟶ ~(◇[n](⋀(◇⁻¹[n]Δ₂))) := contra₀'! (by assumption)
          have : ∅ ⊢ᴹ[Λ]! ~(⋀Δ₁ ⋏ ◇[n](⋀(◇⁻¹[n]Δ₂))) := neg_conj_replace_right! (by assumption) (by assumption);
          have : ∅ ⊢ᴹ[Λ]! ⋀Δ₁ ⟶ ~(◇[n](⋀(◇⁻¹[n]Δ₂))) := imp_eq_mpr'! $ neg_conj'! (by assumption);
          have : ∅ ⊢ᴹ[Λ]! ~(◇[n](⋀(◇⁻¹[n]Δ₂))) ⟶ (□[n](~(⋀◇⁻¹[n]Δ₂))) := contra₂'! $ iff_mpr'! $ multidia_duality!;
          have : ∅ ⊢ᴹ[Λ]! ⋀Δ₁ ⟶ □[n](~⋀◇⁻¹[n]Δ₂) := imp_trans'! (by assumption) (by assumption);
          have : Ω₁ ⊢ᴹ[Λ]! □⋀Δ₁ ⟶ □[(n + 1)](~(⋀◇⁻¹[n]Δ₂)) := box_distribute_nec'! (by assumption);
          have : Ω₁ ⊢ᴹ[Λ]! □[(n + 1)](~⋀◇⁻¹[n]Δ₂) := (by assumption) ⨀ (membership_iff.mp h₁);
          have : □[(n + 1)](~⋀◇⁻¹[n]Δ₂) ∈ Ω₁ := membership_iff.mpr (by assumption);
          exact neg_membership_iff.mp $ h (by assumption);

        contradiction;
      )
      existsi Ω;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih;
        apply (multibox_multidia hK).mpr;
        intro p hp;
        have : ◇[n]p ∈ ◇[n]Ω₂ := Set.multidia_mem_intro hp;
        apply hΩ;
        simp_all;

lemma multiframe_dia : (CanonicalModel Λ).frame[n] Ω₁ Ω₂ ↔ (∀ {p : Formula β}, (p ∈ Ω₂ → ◇[n]p ∈ Ω₁)) := Iff.trans (multiframe_box hK) (multibox_multidia hK)

@[simp]
lemma val_def {a : β} : (CanonicalModel Λ).val Ω a ↔ (atom a) ∈ Ω := by rfl

end CanonicalModel

lemma truthlemma {p : Formula β} : ∀ {Ω}, (Ω ⊩ᴹ[CanonicalModel Λ] p) ↔ (p ∈ Ω) := by
  induction p using rec' with
  | hatom => simp;
  | hfalsum => simp;
  | himp => simp_all [imp_membership_iff'];
  | hor => simp_all [or_membership_iff];
  | hand => simp_all [and_membership_iff];
  | hbox p ih =>
    intro Ω;
    constructor;
    . intro h;
      apply (mct_mem_box_iff hK).mpr;
      intro Ω' hΩ';
      apply ih.mp;
      simp [Satisfies.box_def] at h;
      exact h Ω' hΩ';
    . intro h Ω' hΩ';
      apply ih.mpr;
      simp [Set.subset_def, CanonicalModel.frame_def] at hΩ';
      exact hΩ' h;

lemma truthlemma' {Γ : Theory β} : ∀ {Ω}, (Ω ⊩ᴹ[CanonicalModel Λ] Γ) ↔ (Γ ⊆ Ω.theory) := by
  intro Ω;
  constructor;
  . simp [Set.subset_def];
    intro h p hp;
    exact truthlemma hK |>.mp $ h p hp;
  . intro h p hp;
    apply truthlemma hK |>.mpr;
    apply h hp;

end LO.Modal.Normal

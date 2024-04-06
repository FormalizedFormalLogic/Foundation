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
lemma inconsistent_insert_falsum : Inconsistent Λ (insert ⊥ Γ) := Hilbert.inconsistent_insert_falsum (· ⊢ᴹ[Λ] ·) Γ

lemma consistent_iff_undeducible_falsum : Consistent Λ Γ ↔ (Γ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_iff_undeducible_falsum (· ⊢ᴹ[Λ] ·) Γ

@[simp]
lemma consistent_undeducible_falsum : Γ ⊬ᴹ[Λ]! ⊥ := consistent_iff_undeducible_falsum.mp hConsisΓ

lemma consistent_subset_undeducible_falsum (Δ) (hΔ : Δ ⊆ Γ) : (Δ ⊬ᴹ[Λ]! ⊥) := Hilbert.consistent_subset_undeducible_falsum (· ⊢ᴹ[Λ] ·) hConsisΓ hΔ

lemma consistent_no_falsum : ⊥ ∉ Γ := Hilbert.consistent_no_falsum (· ⊢ᴹ[Λ] ·) hConsisΓ

lemma consistent_no_falsum_subset (hΔ : Δ ⊆ Γ) : ⊥ ∉ Δ := Hilbert.consistent_no_falsum_subset (· ⊢ᴹ[Λ] ·) hConsisΓ hΔ

lemma consistent_neither_undeducible (p) : (Γ ⊬ᴹ[Λ]! p) ∨ (Γ ⊬ᴹ[Λ]! ~p) := Hilbert.consistent_neither_undeducible (· ⊢ᴹ[Λ] ·) hConsisΓ p

lemma consistent_of_subset (h : Γ₁ ⊆ Γ₂) : (Consistent Λ Γ₂) → (Consistent Λ Γ₁) := Hilbert.consistent_of_subset (· ⊢ᴹ[Λ] ·) h

lemma consistent_insert {Γ : Theory β} {p : Formula β} : (Consistent Λ (insert p Γ)) → (Consistent Λ Γ) := consistent_of_subset (by simp)

lemma consistent_empty (hConsisΛ : Theory.Consistent Λ Λ) : Theory.Consistent Λ ∅ := consistent_of_subset (by simp) hConsisΛ

lemma inconsistent_insert (h : Inconsistent Λ (insert p Γ)) : (∃ Δ, (Δ ⊆ Γ) ∧ ((insert p Δ) ⊢ᴹ[Λ]! ⊥)) := Hilbert.inconsistent_insert (· ⊢ᴹ[Λ] ·) h

lemma consistent_iff_insert_neg  : (Consistent Λ (insert (~p) Γ)) ↔ (Γ ⊬ᴹ[Λ]! p)  := Hilbert.consistent_iff_insert_neg (· ⊢ᴹ[Λ] ·)

lemma consistent_either (hConsisΓ : Consistent Λ Γ) : ∀ p, (Consistent Λ (insert p Γ)) ∨ (Consistent Λ (insert (~p) Γ)) := Hilbert.consistent_either (· ⊢ᴹ[Λ] ·) hConsisΓ

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
  have h₂ : {~p} ⊢ᴹ[Λ]! ⊥ := by simpa using dtl! $ dni'! (show ∅ ⊢ᴹ[Λ]! p by exact Deducible.maxm! hp);
  contradiction;

lemma maximal_consistent_iff_membership_deducible : (p ∈ Γ) ↔ (Γ ⊢ᴹ[Λ]! p) := by
  constructor;
  . intro h; exact (Hilbert.axm! h)
  . intro h;
    suffices ~p ∉ Γ by have := hMCΓ.2 p; aesop;
    by_contra hC;
    have h₂ : Γ ⊢ᴹ[Λ]! ~p := Hilbert.axm! hC;
    exact consistent_subset_undeducible_falsum hMCΓ.1 Γ (by simp) (modus_ponens'! h₂ h);

lemma maximal_consistent_iff_not_membership_undeducible : (p ∉ Γ) ↔ (Γ ⊬ᴹ[Λ]! p) := by
  simpa using (maximal_consistent_iff_membership_deducible hMCΓ).not;

lemma maximal_consistent_modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Γ) → (p ∈ Γ) → (q ∈ Γ) := by
  intro hp hpq;
  have dp  := (maximal_consistent_iff_membership_deducible hMCΓ).mp hp;
  have dpq := (maximal_consistent_iff_membership_deducible hMCΓ).mp hpq;
  exact (maximal_consistent_iff_membership_deducible hMCΓ).mpr $ modus_ponens'! dp dpq;

lemma maximal_consistent_neg_membership_iff : (~p ∈ Γ) ↔ (p ∉ Γ) := by
  constructor;
  . intros;
    by_contra hC;
    have hp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hnp : ({p, ~p}) ⊢ᴹ[Λ]! ~p := axm! (by simp);
    apply consistent_subset_undeducible_falsum hMCΓ.1 {p, ~p} (by aesop;) (modus_ponens'! hnp hp);
  . have := hMCΓ.2 p; aesop;

lemma maximal_consistent_imp_membership_iff : (p ⟶ q ∈ Γ) ↔ (p ∉ Γ) ∨ (q ∈ Γ) := by
  constructor;
  . simp [or_iff_not_imp_left];
    intros;
    apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
    have hp : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p := axm! (by simp);
    have hpq : ({p, p ⟶ q}) ⊢ᴹ[Λ]! p ⟶ q := axm! (by simp);
    exact weakening! (by aesop) $ modus_ponens'! hpq hp;
  . intros h;
    cases h;
    case inl h =>
      have := (maximal_consistent_neg_membership_iff hMCΓ).mpr h;
      have d₁ : Γ ⊢ᴹ[Λ]! (~p ⟶ (p ⟶ q)) := by
        have dp : ({p, ~p}) ⊢ᴹ[Λ]! p := axm! (by simp);
        have dnp : ({p, ~p}) ⊢ᴹ[Λ]! (~p) := axm! (by simp);
        have h₂ : ({p, ~p}) ⊢ᴹ[Λ]! q := efq'! $ modus_ponens'! (by simpa using dnp) dp;
        have h₃ : ∅ ⊢ᴹ[Λ]! ~p ⟶ (p ⟶ q) := dtr! (by simpa using dtr! h₂);
        exact weakening! (by simp) h₃;
      have d₂ : Γ ⊢ᴹ[Λ]! ~p := axm! (by simpa)
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact modus_ponens'! d₁ d₂;
    case inr h =>
      have d₁ : Γ ⊢ᴹ[Λ]! (q ⟶ (p ⟶ q)) := imply₁! _ _ _;
      have d₂ : Γ ⊢ᴹ[Λ]! q := axm! h;
      apply (maximal_consistent_iff_membership_deducible hMCΓ).mpr;
      exact modus_ponens'! d₁ d₂;

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

def box := □Ω.theory
prefix:73  "□" => box

def dia := ◇Ω.theory
prefix:73  "◇" => dia

def prebox := □⁻¹Ω.theory
prefix:73  "□⁻¹" => prebox

def predia := ◇⁻¹Ω.theory
prefix:73  "◇⁻¹" => predia

def multibox (n : ℕ) (Ω : MaximalConsistentTheory Λ) := □[n]Ω.theory
notation:73 "□[" n:90 "]" Ω:80 => multibox n Ω

def multidia (n : ℕ) (Ω : MaximalConsistentTheory Λ) := ◇[n]Ω.theory
notation:73 "◇[" n:90 "]" Ω:80 => multidia n Ω

def multiprebox (n : ℕ) (Ω : MaximalConsistentTheory Λ) := □⁻¹[n]Ω.theory
notation:73 "□⁻¹[" n:90 "]" Ω:80 => multiprebox n Ω

def multipredia (n : ℕ) (Ω : MaximalConsistentTheory Λ) := ◇⁻¹[n]Ω.theory
notation:73 "◇⁻¹[" n:90 "]" Ω:80 => multipredia n Ω

variable {Ω : MaximalConsistentTheory Λ}

lemma modus_ponens' {p q : Formula β} : ((p ⟶ q) ∈ Ω) → (p ∈ Ω) → (q ∈ Ω) := by
  apply maximal_consistent_modus_ponens' (Ω.mc);

lemma membership_iff {Ω : MaximalConsistentTheory Λ} {p : Formula β} : (p ∈ Ω) ↔ (Ω.theory ⊢ᴹ[Λ]! p) := by
  apply maximal_consistent_iff_membership_deducible (Ω.mc);

lemma iff_congr : (Ω.theory ⊢ᴹ[Λ]! (p ⟷ q)) → ((p ∈ Ω) ↔ (q ∈ Ω)) := by
  intro hpq;
  simp only [LogicalConnective.iff] at hpq;
  constructor;
  . intro hp;
    exact membership_iff.mpr $ modus_ponens'! (conj₁'! hpq) (membership_iff.mp hp)
  . intro hq;
    exact membership_iff.mpr $ modus_ponens'! (conj₂'! hpq) (membership_iff.mp hq)

lemma dn_membership_iff : (p ∈ Ω) ↔ (~~p ∈ Ω) := iff_congr (equiv_dn! Ω.theory p)

lemma neg_membership_iff : (~p ∈ Ω) ↔ (p ∉ Ω) := maximal_consistent_neg_membership_iff (Ω.mc)

lemma imp_membership_iff' : (p ⟶ q ∈ Ω) ↔ ((p ∈ Ω) → (q ∈ Ω)) := maximal_consistent_imp_membership_iff' (Ω.mc)

lemma and_membership_iff : (p ⋏ q ∈ Ω) ↔ (p ∈ Ω) ∧ (q ∈ Ω) := maximal_consistent_and_membership_iff (Ω.mc)

lemma or_membership_iff : (p ⋎ q ∈ Ω) ↔ (p ∈ Ω) ∨ (q ∈ Ω) := maximal_consistent_or_membership_iff (Ω.mc)

lemma box_dn_membership_iff {p : Formula β} : (□p ∈ Ω) ↔ (□(~~p) ∈ Ω) := by
  have := Deduction.ofKSubset hK;

  constructor;
  . intro h;
    apply membership_iff.mpr;
    have : Ω.theory ⊢ᴹ[Λ]! □(p ⟶ ~~p) := weakening! (show ∅ ⊆ Ω.theory by simp) $ necessitation! $ dni! ∅ _;
    have : Ω.theory ⊢ᴹ[Λ]! □p := membership_iff.mp h;
    have : Ω.theory ⊢ᴹ[Λ]! □~~p := axiomK'! (by assumption) (by assumption);
    assumption;
  . intro h;
    apply membership_iff.mpr;
    have : Ω.theory ⊢ᴹ[Λ]! □(~~p ⟶ p) := weakening! (show ∅ ⊆ Ω.theory by simp) $ necessitation! $ dne! ∅ _;
    have : Ω.theory ⊢ᴹ[Λ]! □~~p := membership_iff.mp h;
    have : Ω.theory ⊢ᴹ[Λ]! □p := axiomK'! (by assumption) (by assumption);
    assumption;

lemma multibox_dn_membership_iff {n : ℕ} {p : Formula β} : (□[n]p ∈ Ω) ↔ (□[n](~~p) ∈ Ω) := by
  induction n generalizing p with
  | zero => simp [-NegDefinition.neg]; exact dn_membership_iff;
  | succ n ih =>
    simp [-NegDefinition.neg];
    have h₁ := @ih (□p);
    rw [←Box.multibox_prepost] at h₁;
    sorry;

lemma box_membership_dual {p : Formula β} : (□p ∈ Ω) ↔ (~(◇(~p)) ∈ Ω) := by
  simp [-NegDefinition.neg];
  constructor;
  . intro h;
    apply dn_membership_iff.mp;
    exact box_dn_membership_iff hK |>.mp h;
  . intro h;
    exact box_dn_membership_iff hK |>.mpr $ dn_membership_iff.mpr h

lemma multidox_membership_dual {n : ℕ} {p : Formula β} : (□[n]p ∈ Ω) ↔ (~(◇[n](~p)) ∈ Ω) := by
  induction n generalizing p with
  | zero => simp [-NegDefinition.neg]; exact dn_membership_iff;
  | succ n ih =>
    simp [-NegDefinition.neg];

    have d₁ : □[n](□p) ∈ Ω ↔ ~(◇[n](~(□p))) ∈ Ω := @ih (□p);
    rw [←Box.multibox_prepost] at d₁;

    have d₂ : (□~(◇[n](~p))) ∈ Ω ↔ ~~(□~(◇[n](~p))) ∈ Ω := dn_membership_iff;


    sorry;
    -- rw [Box.multibox_prepost];
    -- rw [Dia.multidia_prepost];
    -- rw [ih];
    -- simp [-ModalDuality.dia_to_box, -NegDefinition.neg];

lemma dia_membership_dual {p : Formula β} : (◇p ∈ Ω) ↔ (~(□(~p)) ∈ Ω) := by simp;

lemma multidia_membership_prepost {n : ℕ} {p : Formula β} : (◇◇[n]p ∈ Ω) ↔ (◇[n](◇p) ∈ Ω) := by simp only [Dia.multidia_prepost];

lemma mutlidia_membership_prepost' {n : ℕ} {p : Formula β} : (◇[(n + 1)]p ∈ Ω) ↔ (◇[n](◇p) ∈ Ω) := by simp [Dia.multidia_prepost, -ModalDuality.dia_to_box, -NegDefinition.neg];

lemma multidia_dual {n : ℕ} {p : Formula β} : (◇[n]p ∈ Ω) ↔ (~(□[n](~p)) ∈ Ω) := by
  induction n generalizing p with
  | zero => simp [-NegDefinition.neg]; exact dn_membership_iff;
  | succ n ih =>
    simp [-NegDefinition.neg, -ModalDuality.dia_to_box, Dia.multidia_prepost];
    rw [@ih (◇p)];
    simp only [ModalDuality.dia_to_box];
    sorry;

@[simp]
lemma no_falsum : ⊥ ∉ Ω := consistent_no_falsum Ω.consitent

@[simp]
lemma neither_mem : ¬((p ∈ Ω) ∧ (~p ∈ Ω)) := by
  by_contra hC;
  exact Ω.no_falsum $ Ω.modus_ponens' hC.2 hC.1;

/-
@[simp] lemma multibox_zero : (□[0]Ω) = Ω.theory := by sorry; -- simp [Theory.multibox, Set.multibox]

@[simp] lemma multidia_zero : (◇[0]Ω) = Ω.theory := by sorry; -- simp [Theory.multidia, Set.multidia]

@[simp] lemma multiprebox_zero : (□⁻¹[0]Ω) = Ω.theory := by sorry; -- simp [Theory.multiprebox]

@[simp] lemma multipredia_zero : (◇⁻¹[0]Ω) = Ω.theory := by sorry; -- simp [Theory.multipredia, Set.multipredia]
-/

lemma multibox_multidia {Ω₁ Ω₂ : MaximalConsistentTheory Λ} : (∀ {p : Formula β}, (□[n]p ∈ Ω₁ → p ∈ Ω₂)) ↔ (∀ {p : Formula β}, (p ∈ Ω₂ → ◇[n]p ∈ Ω₁)) := by
  constructor;
  . intro h p;
    contrapose;
    intro hp;
    have : ~(◇[n]p) ∈ Ω₁ := neg_membership_iff.mpr hp;
    have : ~~(□[n](~p)) ∈ Ω₁ := by sorry;
    have : □[n](~p) ∈ Ω₁ := dn_membership_iff.mpr this;
    have : ~p ∈ Ω₂ := h this;
    exact neg_membership_iff.mp this;
  . intro h p;
    contrapose;
    intro hp;
    have : ~p ∈ Ω₂ := neg_membership_iff.mpr hp;
    have : ◇[n](~p) ∈ Ω₁ := h this;
    have : ~(□[n](~~p)) ∈ Ω₁ := by sorry;
    have : □[n](~~p) ∉ Ω₁ := neg_membership_iff.mp this;
    sorry;

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

/-
lemma MaximalConsistentTheory.inhabited (h : AxiomSet.Consistent Λ) : Inhabited (MaximalConsistentTheory Λ) := ⟨
  exists_maximal_consistent_theory (by simp only [Theory.Consistent, Theory.Inconsistent];) |>.choose
⟩
-/

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
  induction n generalizing Ω₁ Ω₂ with
  | zero =>
    constructor;
    . intro h; subst h; simp;
    . intro h; apply intro_equality; simpa;
  | succ n ih =>
    constructor;
    . simp;
      intro Ω₃ h₁₃ h₃₂ p h;
      exact ih.mp h₃₂ $ h₁₃ h;
    . intro h;
      obtain ⟨Ω, hΩ⟩ := exists_maximal_consistent_theory (show Consistent Λ (□⁻¹Ω₁ ∪ ◇[n]Ω₂) by sorry)
      existsi Ω;
      constructor;
      . intro p hp;
        apply hΩ;
        simp_all;
      . apply ih.mpr;
        apply multibox_multidia.mpr;
        intro p hp;
        apply hΩ;
        right;
        sorry;

lemma multiframe_dia : (CanonicalModel Λ).frame[n] Ω₁ Ω₂ ↔ (∀ {p : Formula β}, (p ∈ Ω₂ → ◇[n]p ∈ Ω₁)) := Iff.trans multiframe_box multibox_multidia

@[simp]
lemma val_def {a : β} : (CanonicalModel Λ).val Ω a ↔ (atom a) ∈ Ω := by rfl

@[simp]
lemma axiomT (hT : 𝐓 ⊆ Λ) : Reflexive (CanonicalModel Λ).frame := by
  intro Ω p hp;
  have d₁ : Ω.theory ⊢ᴹ[Λ]! (□p ⟶ p) := Deducible.maxm! (hT $ (by apply AxiomT.set.include));
  apply Ω.modus_ponens' (membership_iff.mpr d₁) hp;

@[simp]
lemma axiomD (hD : 𝐃 ⊆ Λ) : Serial (CanonicalModel Λ).frame := by
  have := Deduction.instBoxedNecessitation hK; -- TODO: it can be removed?

  intro Ω;
  simp [frame_def];
  suffices h : Consistent Λ (□⁻¹Ω.theory) by exact exists_maximal_consistent_theory h;
  by_contra hC;
  simp [Theory.Consistent, Theory.Inconsistent] at hC;
  have d₁ : Ω.theory ⊢ᴹ[Λ]! □⊥ := preboxed_necessitation! (Deduction.not_consistent.mp hC);
  have d₂ : Ω.theory ⊢ᴹ[Λ]! (□⊥ ⟶ ◇⊥) := Deducible.maxm! (hD $ (by apply AxiomD.set.include));
  have d₃ : Ω.theory ⊢ᴹ[Λ]! ~(◇⊥) := dni'! $ boxverum! Ω.theory;
  have d₄ : Ω.theory ⊢ᴹ[Λ]! ◇⊥ := modus_ponens'! d₂ d₁;
  have d₅ : Ω.theory ⊢ᴹ[Λ]! ⊥ := modus_ponens'! d₃ d₄;
  exact consistent_undeducible_falsum Ω.consitent d₅;

@[simp]
lemma axiomB (hB : 𝐁 ⊆ Λ) : Symmetric (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ h;
  simp [frame_def] at h;
  simp [(frame_def' hK)];
  intro p hp;
  have ⟨q, hq, _⟩ := Set.dia_mem_iff.mp hp;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! q := membership_iff.mp hq;
  have d₂ : Ω₁.theory ⊢ᴹ[Λ]! (q ⟶ □◇q) := Deducible.maxm! (hB $ (by apply AxiomB.set.include));
  have d₃ : Ω₁.theory ⊢ᴹ[Λ]! □◇q := modus_ponens'! d₂ d₁;
  have := membership_iff.mpr d₃;
  aesop

@[simp]
lemma axiom4 (h4 : 𝟒 ⊆ Λ) : Transitive (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ Ω₃ h₁₂ h₂₃ p hp;
  apply h₂₃;
  apply h₁₂;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! (□p ⟶ □□p) := Deducible.maxm! (h4 $ (by apply Axiom4.set.include));
  exact Ω₁.modus_ponens' (membership_iff.mpr d₁) hp;

@[simp]
lemma axiom5 (h5 : 𝟓 ⊆ Λ) : Euclidean (CanonicalModel Λ).frame := by
  intro Ω₁ Ω₂ Ω₃ h₁₂ h₁₃;
  simp [frame_def] at h₁₂;
  simp [(frame_def' hK)] at h₁₃;
  simp [(frame_def' hK)];
  intro p hp;
  have ⟨q, _, _⟩ := Set.dia_mem_iff.mp hp;
  have d₁ : Ω₁.theory ⊢ᴹ[Λ]! ◇q := axm! (by aesop)
  have d₂ : Ω₁.theory ⊢ᴹ[Λ]! ◇q ⟶ □◇q := Deducible.maxm! (h5 $ (by apply Axiom5.set.include));
  have d₃ : Ω₁.theory ⊢ᴹ[Λ]! □◇q := modus_ponens'! d₂ d₁;
  have := membership_iff.mpr d₃;
  aesop;

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

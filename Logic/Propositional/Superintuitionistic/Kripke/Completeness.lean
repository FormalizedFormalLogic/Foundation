import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

@[simp]
lemma _root_.Set.subset_doubleton {s : Set α} {a b : α} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . aesop;
  . rintro ⟨ha, hb⟩;
    apply Set.insert_subset; exact ha;
    simp_all;

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F} {Γ Δ : Finset F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

variable {Γ Δ : List F}

lemma dhyp! (b : 𝓢 ⊢! p) : 𝓢 ⊢! q ⟶ p := ⟨dhyp _ b.some⟩

lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! Γ.conj) ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ
  case nil => simp;
  case cons p Δ ih =>
    simp;
    constructor
    · intro h; exact ⟨conj₁'! h, ih.mp (conj₂'! h)⟩
    · intro h; exact conj₃'! h.1 (ih.mpr h.2)

lemma implyLeftReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  constructor;
  . exact imp_trans! $ conj₂'! h;
  . exact imp_trans! $ conj₁'! h;

lemma implyRightReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  constructor;
  . intro hrp; exact imp_trans! hrp $ conj₁'! h;
  . intro hrq; exact imp_trans! hrq $ conj₂'! h;

lemma iffDisjSingleton'! [HasEFQ 𝓢] : (𝓢 ⊢! [p].disj) ↔ (𝓢 ⊢! p) := by
  simp [List.disj]
  constructor;
  . intro h; exact disj₃'! (by simp) efq! h;
  . intro h; exact disj₁'! h;

lemma iffDisjSingleton! [HasEFQ 𝓢] : 𝓢 ⊢! [p].disj ⟷ p := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffDisjSingleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffDisjSingleton'!.mpr;
    exact by_axm! (by simp);

def implyOrLeft' (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ (r ⋎ q) := by
  apply emptyPrf;
  apply deduct;
  apply disj₁';
  apply deductInv;
  exact of' h;

lemma implyOrLeft'! (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ (r ⋎ q) := ⟨implyOrLeft' h.some⟩

def implyOrRight' (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ q ⟶ (p ⋎ r) := by
  apply emptyPrf;
  apply deduct;
  apply disj₂';
  apply deductInv;
  exact of' h;

lemma implyOrRight'! (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! q ⟶ (p ⋎ r) := ⟨implyOrRight' h.some⟩

lemma or_assoc'! : 𝓢 ⊢! p ⋎ (q ⋎ r) ↔ 𝓢 ⊢! (p ⋎ q) ⋎ r := by
  constructor;
  . intro h;
    exact disj₃'!
      (by apply implyOrLeft'!; apply implyOrLeft'!; simp;)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have : [q ⋎ r] ⊢[𝓢]! q ⋎ r := by_axm! (by simp);
        exact disj₃'! (by apply implyOrLeft'!; apply implyOrRight'!; simp) (by apply implyOrRight'!; simp) this;
      )
      h;
  . intro h;
    exact disj₃'!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        have : [p ⋎ q] ⊢[𝓢]! p ⋎ q := by_axm! (by simp);
        exact disj₃'! (by apply implyOrLeft'!; simp) (by apply implyOrRight'!; apply implyOrLeft'!; simp) this;
      )
      (by apply implyOrRight'!; apply implyOrRight'!; simp;)
      h;

lemma iffDisjDoubleton'! [HasEFQ 𝓢] : (𝓢 ⊢! [p, q].disj) ↔ (𝓢 ⊢! p ⋎ q) := by
  simp [List.disj];
  constructor;
  . intro h; exact disj₃'! imp_id! efq! (or_assoc'!.mp h);
  . intro h; exact disj₃'! (by simp) (imp_trans! (show 𝓢 ⊢! q ⟶ q ⋎ ⊥ by simp) (by simp)) h;

lemma iffDisjDoubleton! [HasEFQ 𝓢] : 𝓢 ⊢! [p, q].disj ⟷ p ⋎ q := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffDisjDoubleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffDisjDoubleton'!.mpr;
    exact by_axm! (by simp);

lemma implyRightDisjSingleton'! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ [q].disj) ↔ (𝓢 ⊢! p ⟶ q) := implyRightReplaceIff'! iffDisjSingleton!

lemma implyLeftDisjSingleton'! [HasEFQ 𝓢] : (𝓢 ⊢! ([p].disj) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := implyLeftReplaceIff'! iffDisjSingleton!

lemma implyRightDisjDoubleton'! [HasEFQ 𝓢] : (𝓢 ⊢! p ⟶ [q, r].disj) ↔ (𝓢 ⊢! p ⟶ q ⋎ r) := implyRightReplaceIff'! iffDisjDoubleton!

lemma implyLeftDisjDoubleton'! [HasEFQ 𝓢] : (𝓢 ⊢! ([p, q].disj) ⟶ r) ↔ (𝓢 ⊢! (p ⋎ q) ⟶ r) := implyLeftReplaceIff'! iffDisjDoubleton!

lemma iffConjSingleton'! : (𝓢 ⊢! [p].conj) ↔ (𝓢 ⊢! p) := by
  simp [List.conj];
  constructor;
  . intro h; exact conj₁'! h;
  . intro h; exact conj₃'! h (by simp)

lemma iffConjSingleton! : 𝓢 ⊢! [p].conj ⟷ p := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjSingleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjSingleton'!.mpr;
    exact by_axm! (by simp);

lemma iffConjDoubleton'! : 𝓢 ⊢! [p, q].conj ↔ 𝓢 ⊢! p ⋏ q := by
  simp [List.conj];
  constructor;
  . intro h; exact conj₃'! (conj₁'! h) (conj₁'! $ conj₂'! h);
  . intro h; exact conj₃'! (conj₁'! h) (conj₃'! (conj₂'! h) (by simp));

lemma iffConjDoubleton! : 𝓢 ⊢! [p, q].conj ⟷ p ⋏ q := by
  apply iff_intro!;
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjDoubleton'!.mp;
    exact by_axm! (by simp);
  . apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    apply iffConjDoubleton'!.mpr;
    exact by_axm! (by simp);

def iffId (p : F) : 𝓢 ⊢ p ⟷ p := conj₃' (impId p) (impId p)
@[simp] def iff_id! : 𝓢 ⊢! p ⟷ p := ⟨iffId p⟩

lemma implyLeftConjEmpty'! : (𝓢 ⊢! ([].conj) ⟶ p) ↔ (𝓢 ⊢! p) := by
  simp;
  constructor;
  . intro h; exact h ⨀ (by simp);
  . intro h; exact dhyp! h;

lemma implyRightConjSingleton'! : (𝓢 ⊢! p ⟶ [q].conj) ↔ (𝓢 ⊢! p ⟶ q) := implyRightReplaceIff'! iffConjSingleton!

lemma implyLeftConjSingleton'! : (𝓢 ⊢! ([p].conj) ⟶ q) ↔ (𝓢 ⊢! p ⟶ q) := implyLeftReplaceIff'! iffConjSingleton!

lemma implyRightConjDoubleton'! : (𝓢 ⊢! p ⟶ [q, r].conj) ↔ (𝓢 ⊢! p ⟶ q ⋏ r) := implyRightReplaceIff'! iffConjDoubleton!

lemma implyLeftConjDoubleton'! : (𝓢 ⊢! ([p, q].conj) ⟶ r) ↔ (𝓢 ⊢! (p ⋏ q) ⟶ r) := implyLeftReplaceIff'! iffConjDoubleton!

@[simp]
lemma forthbackConjRemove : 𝓢 ⊢! (Γ.remove p).conj ⋏ p ⟶ Γ.conj := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have d : [(Γ.remove p).conj ⋏ p] ⊢[𝓢]! (Γ.remove p).conj ⋏ p := by_axm! (by simp);
  apply iff_provable_list_conj.mpr;
  intro q hq;
  by_cases e : q = p;
  . subst e; exact conj₂'! d;
  . exact iff_provable_list_conj.mp (conj₁'! d) q (by apply List.mem_remove_iff.mpr; simp_all);

lemma implyLeftRemoveConj (hC : 𝓢 ⊢! Γ.conj ⟶ q) : 𝓢 ⊢! (Γ.remove p).conj ⋏ p ⟶ q := by
  exact imp_trans! (by simp) hC;

lemma orRightImplyRight'! (hpr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ (r ⋎ q) := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  replace hpr : [p] ⊢[𝓢]! p ⟶ r := weakening! (by simp) $ provable_iff_provable.mp hpr;
  have hp : [p] ⊢[𝓢]! p := by_axm! (by simp);
  exact disj₁'! (hpr ⨀ hp);

lemma what [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) (h : 𝓢 ⊢! Γ.disj) : 𝓢 ⊢! p := by
  induction Γ with
  | nil => exact efq! ⨀ h;
  | cons x xs ih =>
    simp at h;
    simp at hd;
    have ⟨hd₁, hd₂⟩ := hd;
    exact disj₃'! (by subst hd₁; simp;) (by sorry) h;

end LO.System

namespace LO.Propositional.Superintuitionistic

variable [DecidableEq α]

-- instance : Coe (List (Formula α)) (Theory α) := ⟨λ Γ => ↑Γ.toFinset⟩

open System FiniteContext
open Formula Formula.Kripke

variable {Λ : AxiomSet α} [HasEFQ Λ]

def Tableau (α) := Theory α × Theory α

namespace Tableau

instance : HasSubset (Tableau α) := ⟨λ t₁ t₂ => t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2⟩

@[simp] lemma subset_def {t₁ t₂ : Tableau α} : t₁ ⊆ t₂ ↔ t₁.1 ⊆ t₂.1 ∧ t₁.2 ⊆ t₂.2 := by rfl

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ t.1) → (∀ p ∈ Δ, p ∈ t.2) → Λ ⊬! Γ.conj ⟶ Δ.disj

variable (hCon : Consistent Λ t)

def consistent_either (p : Formula α) : Consistent Λ (insert p t.1, t.2) ∨ Consistent Λ (t.1, insert p t.2) := by
  by_contra hC;
  obtain ⟨⟨Γ₁, hΓ₁, Δ₁, hΔ₁, hC₁⟩, ⟨Γ₂, hΓ₂, Δ₂, hΔ₂, hC₂⟩⟩ := by simpa only [Consistent, not_or, not_forall, not_not, exists_prop, exists_and_left] using hC;
  simp_all;
  sorry;
  -- replace hC₁ : Λ ⊢! ⋀(Γ₁.remove p) ⋏ p ⟶ ⋁Δ₁ := implyLeftRemoveConj hC₁;
  -- replace hC₂ : Λ ⊢! ⋀Γ₂ ⟶ ⋁(Δ₂.remove p) ⋎ p := implyRightRemoveDisj hC₂;
  -- have : Λ ⊢! ⋀(Γ₁.remove p) ⋏ p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂) := imp_trans! hC₁ (by simp)
  -- have : Λ ⊢! ⋀(Γ₁.remove p) ⟶ (p ⟶ (⋁Δ₁ ⋎ ⋁Δ₂)) := andImplyIffImplyImply'!.mp this;
  -- sorry;

lemma disjoint_of_consistent : Disjoint t.1 t.2 := by
  by_contra h;
  obtain ⟨T, hp₂, hp₁, hp⟩ := by simpa [Disjoint] using h;
  obtain ⟨p, hp, _⟩ := Set.not_subset.mp hp;
  simp [Consistent] at hCon;
  have : Λ ⊬! [p].conj ⟶ [p].disj := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : Λ ⊢! [p].conj ⟶ [p].disj := by
    apply implyLeftConjSingleton'!.mpr;
    apply implyRightDisjSingleton'!.mpr;
    simp;
  contradiction;

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.1) (h : Λ ⊢! Γ.conj ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! Γ.conj ⟶ [q].disj := implyRightDisjSingleton'!.mpr h;
  have : Λ ⊬! Γ.conj ⟶ [q].disj := hCon (by aesop) (by aesop);
  contradiction;

def Saturated (t : Tableau α) := ∀ p : Formula α, p ∈ t.1 ∨ p ∈ t.2

variable (hMat : Saturated t := by simpa)

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

section lindenbaum

lemma lindenbaum (hCon : Consistent Λ t₀) : ∃ t, t₀ ⊆ t ∧ (Consistent Λ t) ∧ (Saturated t) := by sorry;

end lindenbaum

end Tableau

structure SaturatedConsistentTableau (Λ : AxiomSet α) where
  tableau : Tableau α
  saturated : tableau.Saturated
  consistent : tableau.Consistent Λ

namespace SaturatedConsistentTableau

lemma lindenbaum (hCon : t₀.Consistent Λ) : ∃ (t : SaturatedConsistentTableau Λ), t₀ ⊆ t.tableau := by
  obtain ⟨t, ht, hCon, hMax⟩ := Tableau.lindenbaum hCon;
  exact ⟨⟨t, hMax, hCon⟩, ht⟩;

variable (t : SaturatedConsistentTableau Λ)

@[simp] lemma disjoint : Disjoint t.tableau.1 t.tableau.2 := t.tableau.disjoint_of_consistent t.consistent

lemma not_mem₁_iff_mem₂ : p ∉ t.tableau.1 ↔ p ∈ t.tableau.2 := Tableau.not_mem₁_iff_mem₂ t.consistent t.saturated

lemma not_mem₂_iff_mem₁ : p ∉ t.tableau.2 ↔ p ∈ t.tableau.1 := Tableau.not_mem₂_iff_mem₁ t.consistent t.saturated

variable {t : SaturatedConsistentTableau Λ}

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.tableau.1) (h : Λ ⊢! Γ.conj ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp (hp : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  exact t.not_mem₂_iff_mem₁.mp $ not_mem₂ (by simpa) (show Λ ⊢! List.conj [p] ⟶ q by apply implyLeftConjSingleton'!.mpr; assumption)

@[simp]
lemma verum : ⊤ ∈ t.tableau.1 := by
  apply t.not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : Λ ⊬! [].conj ⟶ [⊤].disj := t.consistent (by simp) (by simpa);
  have : Λ ⊢! [].conj ⟶ [⊤].disj := by simp;
  contradiction;

@[simp]
lemma falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! [⊥].conj ⟶ [].disj := t.consistent (by simpa) (by simp);
  have : Λ ⊢! [⊥].conj ⟶ [].disj := by simp;
  contradiction;

@[simp]
lemma conj : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp h (by simp)
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    have : Λ ⊢! [p, q].conj ⟶ [p ⋏ q].disj := by
      apply implyRightDisjSingleton'!.mpr;
      apply implyLeftConjDoubleton'!.mpr;
      apply imp_id!;
    have : Λ ⊬! [p, q].conj ⟶ [p ⋏ q].disj := t.consistent (by aesop) (by simpa using t.mem_either₁.mp hC);
    contradiction;

@[simp]
lemma disj : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.1;
    have : q ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.2;
    have : Λ ⊢! [p ⋎ q].conj ⟶ [p, q].disj := by
      apply implyRightDisjDoubleton'!.mpr;
      apply implyLeftConjSingleton'!.mpr;
      apply imp_id!;
    have : Λ ⊬! [p ⋎ q].conj ⟶ [p, q].disj := t.consistent (by simp_all) (by simp_all);
    contradiction;
  . intro h;
    cases h with
    | inl h => exact mdp h disj₁!
    | inr h => exact mdp h disj₂!

end SaturatedConsistentTableau


namespace Kripke

def CanonicalModel (Λ : AxiomSet α) : Model (𝐈𝐧𝐭 (SaturatedConsistentTableau Λ) α) where
  frame := λ t₁ t₂ => t₁.tableau.1 ⊆ t₂.tableau.1
  valuation := λ t a => (atom a) ∈ t.tableau.1
  hereditary := by aesop;
  frame_prop := by simp [FrameClass.Intuitionistic, Transitive, Reflexive]; tauto;

namespace CanonicalModel

@[simp] lemma frame_def {t₁ t₂ : SaturatedConsistentTableau Λ} : (CanonicalModel Λ).frame t₁ t₂ ↔ t₁.tableau.1 ⊆ t₂.tableau.1 := by rfl
@[simp] lemma valuation_def {t : SaturatedConsistentTableau Λ} {a : α} : (CanonicalModel Λ).valuation t a ↔ (atom a) ∈ t.tableau.1 := by rfl

end CanonicalModel

variable {t : SaturatedConsistentTableau Λ}

lemma truthlemma : ((CanonicalModel Λ), t) ⊧ p ↔ p ∈ t.tableau.1 := by
  induction p using rec' generalizing t with
  | himp p q ihp ihq =>
    constructor;
    . contrapose;
      intro h;
      simp [Satisfies.imp_def];
      replace h := t.not_mem₁_iff_mem₂.mp h;
      have : Tableau.Consistent Λ (insert p t.tableau.1, {q}) := by
        simp only [Tableau.Consistent];
        intro Γ Δ hΓ hΔ;
        replace hΓ : ∀ r, r ∈ Γ.remove p → r ∈ t.tableau.1 := by
          intro r hr;
          have ⟨hr₁, hr₂⟩ := List.mem_remove_iff.mp hr;
          have := hΓ r hr₁;
          simp_all;
        -- replace hΔ : Δ = [] ∨ Δ = [q] := by sorry;
        by_contra hC;
        have : Λ ⊢! (Γ.remove p).conj ⟶ (p ⟶ Δ.disj) := andImplyIffImplyImply'!.mp $ implyLeftRemoveConj hC;
        have : Λ ⊢! (Γ.remove p).conj ⟶ (p ⟶ q) :=  imp_trans! this (by
          apply provable_iff_provable.mpr;
          apply deduct_iff.mpr;
          apply deduct_iff.mpr;
          have d₁ : [p, p ⟶ Δ.disj] ⊢[Λ]! p := by_axm! (by simp);
          have d₂ : [p, p ⟶ Δ.disj] ⊢[Λ]! p ⟶ Δ.disj := by_axm! (by simp);
          have d₃ : [p, p ⟶ Δ.disj] ⊢[Λ]! Δ.disj := d₂ ⨀ d₁;
          -- have : Λ ⊢! q := what (by sorry) d₃;
          -- exact efq'! $ d₂ ⨀ d₁;
          sorry;
        );
        have : Λ ⊢! (Γ.remove p).conj ⟶ [p ⟶ q].disj := implyRightDisjSingleton'!.mpr this;
        have : Λ ⊬! (Γ.remove p).conj ⟶ [p ⟶ q].disj := t.consistent (by simp_all) (by simpa using h);
        contradiction;
        /-
        have : Λ ⊢! (Γ.remove p).conj ⟶ (p ⟶ q) := by
          cases hΔ with
          | inl h =>
            subst h;
            simp [Finset.disj] at hC;
            have : Λ ⊢! ((Γ.remove p).conj ⋏ p) ⟶ ⊥ := implyLeftRemoveConj hC;
            have : Λ ⊢! (Γ.remove p).conj ⟶ (p ⟶ ⊥) := andImplyIffImplyImply'!.mp this;
            exact imp_trans! this (by
              apply provable_iff_provable.mpr;
              apply deduct_iff.mpr;
              apply deduct_iff.mpr;
              have d₁ : [p, p ⟶ ⊥] ⊢[Λ]! p := by_axm! (by simp);
              have d₂ : [p, p ⟶ ⊥] ⊢[Λ]! p ⟶ ⊥ := by_axm! (by simp);
              exact efq'! $ d₂ ⨀ d₁;
            );
          | inr h =>
            subst h;
            have : Λ ⊢! ((Γ.remove p).conj ⋏ p) ⟶ q := implyLeftRemoveConj $ implyRightDisjSingleton'!.mp hC;
            exact andImplyIffImplyImply'!.mp this;
        -/
      obtain ⟨t', ⟨⟨_, _⟩, _⟩⟩ := by simpa [Set.insert_subset_iff] using SaturatedConsistentTableau.lindenbaum this;
      existsi t';
      simp_all;
      apply t'.not_mem₁_iff_mem₂.mpr;
      simpa
    . simp [Satisfies.imp_def];
      intro h t' htt' hp;
      replace hp := ihp.mp hp;
      have hpq := htt' h;
      apply ihq.mpr;
      apply t'.not_mem₂_iff_mem₁.mp;
      exact SaturatedConsistentTableau.not_mem₂
        (by simp_all;)
        (show Λ ⊢! [p, p ⟶ q].conj ⟶ q by
          apply implyLeftConjDoubleton'!.mpr;
          apply provable_iff_provable.mpr;
          apply deduct_iff.mpr;
          have : [p ⋏ (p ⟶ q)] ⊢[Λ]! p ⋏ (p ⟶ q) := by_axm! (by simp);
          exact (conj₂'! this) ⨀ (conj₁'! this);
        );
  | _ => simp [Satisfies.iff_models, Satisfies, *];

lemma _root_.List.empty_def {Γ : List α} : Γ = [] ↔ ∀ p, p ∉ Γ := by induction Γ <;> simp_all;


lemma deducible_of_validOnCanonicelModel : (CanonicalModel Λ) ⊧ p → Λ ⊢! p := by
  contrapose;
  intro h;
  have : Tableau.Consistent Λ (∅, {p}) := by
    simp only [Tableau.Consistent, Collection.not_mem_empty, imp_false, Set.mem_singleton_iff];
    rintro Γ Δ hΓ hΔ;
    by_contra hC;
    replace hΓ : Γ = [] := List.empty_def.mpr hΓ;
    subst hΓ;
    have : Λ ⊢! p := what hΔ $ implyLeftConjEmpty'!.mp hC;
    contradiction;
  obtain ⟨t', ht'⟩ := SaturatedConsistentTableau.lindenbaum this;
  simp [ValidOnModel.iff_models, ValidOnModel]
  existsi t';
  apply truthlemma.not.mpr;
  apply t'.not_mem₁_iff_mem₂.mpr;
  simp_all;

lemma complete! : (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) ⊧ p → 𝐄𝐅𝐐 ⊢! p := by
  contrapose;
  intro h₁ h₂;
  simp [ValidOnFrameClass.iff_models, ValidOnFrameClass] at h₂;
  have : 𝐄𝐅𝐐 ⊢! p := deducible_of_validOnCanonicelModel $ @h₂ (CanonicalModel 𝐄𝐅𝐐);
  contradiction;

instance : Complete (𝐄𝐅𝐐 : AxiomSet α) (𝐈𝐧𝐭 (SaturatedConsistentTableau (𝐄𝐅𝐐 : AxiomSet α)) α) := ⟨complete!⟩

end Kripke

end LO.Propositional.Superintuitionistic

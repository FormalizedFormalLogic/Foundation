import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

namespace Set

@[simp]
lemma subset_doubleton {s : Set α} {a b : α} : {a, b} ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . aesop;
  . rintro ⟨ha, hb⟩;
    apply Set.insert_subset; exact ha;
    simp_all;

end Set


namespace List

open LO

variable {F : Type u} [LogicalConnective F]
variable {p q : F}

def conj' : List F → F
| [] => ⊤
| [p] => p
| p :: q :: rs => p ⋏ (q :: rs).conj'

@[simp] lemma conj'_nil : conj' (F := F) [] = ⊤ := rfl

@[simp] lemma conj'_singleton : [p].conj' = p := rfl

@[simp] lemma conj'_doubleton : [p, q].conj' = p ⋏ q := rfl

@[simp] lemma conj'_cons_nonempty {a : F} {as : List F} (h : as ≠ []) : (a :: as).conj' = a ⋏ as.conj' := by
  cases as with
  | nil => contradiction;
  | cons q rs => simp [List.conj']

def disj' : List F → F
| [] => ⊥
| [p] => p
| p :: q :: rs => p ⋎ (q :: rs).disj'

@[simp] lemma disj'_nil : disj' (F := F) [] = ⊥ := rfl

@[simp] lemma disj'_singleton : [p].disj' = p := rfl

@[simp] lemma disj'_doubleton : [p, q].disj' = p ⋎ q := rfl

@[simp] lemma disj'_cons_nonempty {a : F} {as : List F} (h : as ≠ []) : (a :: as).disj' = a ⋎ as.disj' := by
  cases as with
  | nil => contradiction;
  | cons q rs => simp [List.disj']

lemma induction₂
  {motive : List F → Prop}
  (hnil : motive [])
  (hsingle : ∀ a, motive [a])
  (hcons : ∀ a as, as ≠ [] → motive as → motive (a :: as)) : ∀ as, motive as := by
  intro as;
  induction as with
  | nil => exact hnil;
  | cons a as ih => cases as with
    | nil => exact hsingle a;
    | cons b bs => exact hcons a (b :: bs) (by simp) ih;

end List


namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F} {Γ Δ : Finset F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

variable {Γ Δ : List F}

lemma dhyp! (b : 𝓢 ⊢! p) : 𝓢 ⊢! q ⟶ p := ⟨dhyp _ b.some⟩

lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! Γ.conj') ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ using List.induction₂ with
  | hnil => simp;
  | hsingle => simp;
  | hcons p Γ hΓ ih =>
    simp_all;
    constructor;
    . intro h;
      constructor;
      . exact conj₁'! h;
      . exact ih.mp (conj₂'! h);
    . rintro ⟨h₁, h₂⟩;
      exact conj₃'! h₁ (ih.mpr h₂);

lemma implyLeftReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  constructor;
  . exact imp_trans! $ conj₂'! h;
  . exact imp_trans! $ conj₁'! h;

lemma implyRightReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  constructor;
  . intro hrp; exact imp_trans! hrp $ conj₁'! h;
  . intro hrq; exact imp_trans! hrq $ conj₂'! h;

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

def iffId (p : F) : 𝓢 ⊢ p ⟷ p := conj₃' (impId p) (impId p)
@[simp] def iff_id! : 𝓢 ⊢! p ⟷ p := ⟨iffId p⟩


@[simp]
lemma forthbackConjRemove : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ Γ.conj' := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have d : [(Γ.remove p).conj' ⋏ p] ⊢[𝓢]! (Γ.remove p).conj' ⋏ p := by_axm! (by simp);
  apply iff_provable_list_conj.mpr;
  intro q hq;
  by_cases e : q = p;
  . subst e; exact conj₂'! d;
  . exact iff_provable_list_conj.mp (conj₁'! d) q (by apply List.mem_remove_iff.mpr; simp_all);

lemma implyLeftRemoveConj (b : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ q := imp_trans! (by simp) b

lemma disj_allsame! [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) : 𝓢 ⊢! Γ.disj' ⟶ p := by
  induction Γ using List.induction₂ with
  | hnil => simp_all [List.disj'_nil, efq!];
  | hsingle => simp_all [List.mem_singleton, List.disj'_singleton, imp_id!];
  | hcons q Δ hΔ ih =>
    simp [List.disj'_cons_nonempty hΔ];
    simp at hd;
    have ⟨hd₁, hd₂⟩ := hd;
    subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact disj₃'!
      (by simp)
      (weakening! (by simp) $ provable_iff_provable.mp $ ih hd₂)
      (show [q ⋎ List.disj' Δ] ⊢[𝓢]! q ⋎ List.disj' Δ by exact by_axm! (by simp));

lemma disj_allsame'! [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) (h : 𝓢 ⊢! Γ.disj') : 𝓢 ⊢! p := (disj_allsame! hd) ⨀ h

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

def Consistent (Λ : AxiomSet α) (t : Tableau α) := ∀ {Γ Δ : List (Formula α)}, (∀ p ∈ Γ, p ∈ t.1) → (∀ p ∈ Δ, p ∈ t.2) → Λ ⊬! Γ.conj' ⟶ Δ.disj'

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
  have : Λ ⊬! [p].conj' ⟶ [p].disj' := hCon
    (by simp_all; apply hp₁; assumption)
    (by simp_all; apply hp₂; assumption);
  have : Λ ⊢! [p].conj' ⟶ [p].disj' := by simp;
  contradiction;

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.1) (h : Λ ⊢! Γ.conj' ⟶ q) : q ∉ t.2 := by
  by_contra hC;
  have : Λ ⊢! Γ.conj' ⟶ [q].disj' := by simpa;
  have : Λ ⊬! Γ.conj' ⟶ [q].disj' := hCon (by aesop) (by aesop);
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

lemma not_mem₂ {Γ : List (Formula α)} (hΓ : ∀ p ∈ Γ, p ∈ t.tableau.1) (h : Λ ⊢! Γ.conj' ⟶ q) : q ∉ t.tableau.2 := t.tableau.not_mem₂ t.consistent hΓ h

lemma mdp (hp : p ∈ t.tableau.1) (h : Λ ⊢! p ⟶ q) : q ∈ t.tableau.1 := by
  exact t.not_mem₂_iff_mem₁.mp $ not_mem₂ (by simpa) (show Λ ⊢! List.conj' [p] ⟶ q by simpa;)

@[simp]
lemma mem_verum : ⊤ ∈ t.tableau.1 := by
  apply t.not_mem₂_iff_mem₁.mp;
  by_contra hC;
  have : Λ ⊬! [].conj' ⟶ [⊤].disj' := t.consistent (by simp) (by simpa);
  have : Λ ⊢! [].conj' ⟶ [⊤].disj' := by simp;
  contradiction;

@[simp]
lemma not_mem_falsum : ⊥ ∉ t.tableau.1 := by
  by_contra hC;
  have : Λ ⊬! [⊥].conj' ⟶ [].disj' := t.consistent (by simpa) (by simp);
  have : Λ ⊢! [⊥].conj' ⟶ [].disj' := by simp;
  contradiction;

@[simp]
lemma iff_mem_conj : p ⋏ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∧ q ∈ t.tableau.1 := by
  constructor;
  . intro h; constructor <;> exact mdp h (by simp)
  . rintro ⟨hp, hq⟩;
    by_contra hC;
    have : Λ ⊢! [p, q].conj' ⟶ [p ⋏ q].disj' := by simp;
    have : Λ ⊬! [p, q].conj' ⟶ [p ⋏ q].disj' := t.consistent (by aesop) (by simpa using t.not_mem₁_iff_mem₂.mp hC);
    contradiction;

@[simp]
lemma iff_mem_disj : p ⋎ q ∈ t.tableau.1 ↔ p ∈ t.tableau.1 ∨ q ∈ t.tableau.1 := by
  constructor;
  . intro h;
    by_contra hC; simp [not_or] at hC;
    have : p ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.1;
    have : q ∈ t.tableau.2 := t.not_mem₁_iff_mem₂.mp hC.2;
    have : Λ ⊢! [p ⋎ q].conj' ⟶ [p, q].disj' := by simp;
    have : Λ ⊬! [p ⋎ q].conj' ⟶ [p, q].disj' := t.consistent (by simp_all) (by simp_all);
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
          have := by simpa using hΓ r hr₁;
          simp_all;
        by_contra hC;
        have : Λ ⊢! (Γ.remove p).conj' ⟶ (p ⟶ q) := imp_trans! (andImplyIffImplyImply'!.mp $ implyLeftRemoveConj hC) (by
          apply provable_iff_provable.mpr;
          apply deduct_iff.mpr;
          apply deduct_iff.mpr;
          have : [p, p ⟶ Δ.disj'] ⊢[Λ]! p := by_axm! (by simp);
          have : [p, p ⟶ Δ.disj'] ⊢[Λ]! Δ.disj' := (by_axm! (by simp)) ⨀ this;
          exact disj_allsame'! (by simpa using hΔ) this;
        )
        have : Λ ⊬! (Γ.remove p).conj' ⟶ (p ⟶ q) := by simpa only [List.disj'_singleton] using (t.consistent hΓ (show ∀ r ∈ [p ⟶ q], r ∈ t.tableau.2 by simp_all));
        contradiction;
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
        (by simp_all)
        (show Λ ⊢! [p, p ⟶ q].conj' ⟶ q by
          simp;
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
    have : Λ ⊢! p := disj_allsame'! hΔ (hC ⨀ verum!);
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

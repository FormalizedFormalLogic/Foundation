import Logic.Logic.System
import Logic.Logic.HilbertStyle.Context

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F}
variable {Γ Δ : List F}

variable {𝓢 : S}
variable [Minimal 𝓢]

open FiniteContext

lemma orComm : 𝓢 ⊢ p ⋎ q ⟶ q ⋎ p := by
  apply emptyPrf;
  apply deduct;
  have : [p ⋎ q] ⊢[𝓢] p ⋎ q := FiniteContext.byAxm (by simp);
  exact disj₃' disj₂ disj₁ this;
lemma orComm! : 𝓢 ⊢! p ⋎ q ⟶ q ⋎ p := ⟨orComm⟩

lemma orComm' (h : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ q ⋎ p := orComm ⨀ h
lemma orComm'! (h : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! q ⋎ p := ⟨orComm' h.some⟩

def dni : 𝓢 ⊢ p ⟶ ~~p := by
  simp [NegDefinition.neg];
  apply emptyPrf;
  apply deduct;
  apply deduct;
  have d₁ : [p ⟶ ⊥, p] ⊢[𝓢] p ⟶ ⊥ := FiniteContext.byAxm (by simp);
  have d₂ : [p ⟶ ⊥, p] ⊢[𝓢] p := FiniteContext.byAxm (by simp);
  exact d₁ ⨀ d₂
@[simp] lemma dni! : 𝓢 ⊢! p ⟶ ~~p := ⟨dni⟩

def dni' (b : 𝓢 ⊢ p) : 𝓢 ⊢ ~~p := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! p) : 𝓢 ⊢! ~~p := ⟨dni' b.some⟩


def contra₀ : 𝓢 ⊢ (p ⟶ q) ⟶ (~q ⟶ ~p) := by
  simp [NegDefinition.neg];
  apply emptyPrf;
  apply deduct;
  apply deduct;
  apply deduct;
  have d₁ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] p := FiniteContext.byAxm (by simp);
  have d₂ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] q ⟶ ⊥ := FiniteContext.byAxm (by simp);
  have d₃ : [p, q ⟶ ⊥, p ⟶ q] ⊢[𝓢] p ⟶ q := FiniteContext.byAxm (by simp);
  exact d₂ ⨀ (d₃ ⨀ d₁);
@[simp] def contra₀! : 𝓢 ⊢! (p ⟶ q) ⟶ (~q ⟶ ~p) := ⟨contra₀⟩

def contra₀' (b : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~q ⟶ ~p := contra₀ ⨀ b
@[simp] def contra₀'! (b : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~q ⟶ ~p := ⟨contra₀' b.some⟩


def tne : 𝓢 ⊢ ~(~~p) ⟶ ~p := contra₀' dni
@[simp] lemma tne! : 𝓢 ⊢! ~(~~p) ⟶ ~p := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ~(~~p)) : 𝓢 ⊢ ~p := tne ⨀ b
@[simp] lemma tne'! (b : 𝓢 ⊢! ~(~~p)) : 𝓢 ⊢! ~p := ⟨tne' b.some⟩

lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! Γ.conj') ↔ (∀ p ∈ Γ, 𝓢 ⊢! p) := by
  induction Γ using List.induction_with_singleton with
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
  induction Γ using List.induction_with_singleton with
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

instance [HasDNE 𝓢] : HasEFQ 𝓢 where
  efq p := by
    have h₁ : 𝓢 ⊢ ⊥ ⟶ (p ⟶ ⊥) ⟶ ⊥ := imply₁
    have h₂ : 𝓢 ⊢ ((p ⟶ ⊥) ⟶ ⊥) ⟶ p := by sorry;
    sorry;
    -- exact dtr' $ h₂ ⨀ (h₁ ⨀ (axm (by simp)));

instance [HasDNE 𝓢] : HasLEM 𝓢 where
  lem p := by sorry;

/-
instance [HasLEM 𝓢] [HasEFQ 𝓢] : HasDNE 𝓢 where
  dne p := by sorry;
-/

end LO.System

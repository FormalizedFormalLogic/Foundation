import Logic.Logic.System
import Logic.Logic.HilbertStyle.Context

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [System F S]
         {𝓢 : S} [Minimal 𝓢]
         {p q r : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext

def bot_of_mem_either [System.NegationEquiv 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] p := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢] p ⟶ ⊥ := NegationEquiv.neg_equiv'.mp $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

@[simp] lemma bot_of_mem_either! [System.NegationEquiv 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩


def efq_of_mem_either [System.NegationEquiv 𝓢] [HasEFQ 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢] q := efq' $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [System.NegationEquiv 𝓢] [HasEFQ 𝓢] (h₁ : p ∈ Γ) (h₂ : ~p ∈ Γ) : Γ ⊢[𝓢]! q := ⟨efq_of_mem_either h₁ h₂⟩

lemma efq_of_neg! [System.NegationEquiv 𝓢] [HasEFQ 𝓢] (h : 𝓢 ⊢! ~p) : 𝓢 ⊢! p ⟶ q := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [p] ⊢[𝓢]! p ⟶ ⊥ := of'! $ neg_equiv'!.mp h;
  exact efq'! (dnp ⨀ FiniteContext.id!);


def orComm : 𝓢 ⊢ p ⋎ q ⟶ q ⋎ p := by
  apply deduct';
  exact disj₃' disj₂ disj₁ $ FiniteContext.id
lemma orComm! : 𝓢 ⊢! p ⋎ q ⟶ q ⋎ p := ⟨orComm⟩

def orComm' (h : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ q ⋎ p := orComm ⨀ h
lemma orComm'! (h : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! q ⋎ p := ⟨orComm' h.some⟩

def implyRightAnd (hq : 𝓢 ⊢ p ⟶ q) (hr : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ q ⋏ r := by
  apply deduct';
  replace hq : [] ⊢[𝓢] p ⟶ q := of hq;
  replace hr : [] ⊢[𝓢] p ⟶ r := of hr;
  exact conj₃' (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
lemma implyRightAnd! (hq : 𝓢 ⊢! p ⟶ q) (hr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ q ⋏ r := ⟨implyRightAnd hq.some hr.some⟩


def andReplaceLeft' (hc : 𝓢 ⊢ p ⋏ q) (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ r ⋏ q := conj₃' (h ⨀ conj₁' hc) (conj₂' hc)
lemma andReplaceLeft'! (hc : 𝓢 ⊢! p ⋏ q) (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! r ⋏ q := ⟨andReplaceLeft' hc.some h.some⟩

def andReplaceLeft (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⋏ q ⟶ r ⋏ q := by
  apply deduct';
  exact andReplaceLeft' FiniteContext.id (of h)
lemma andReplaceLeft! (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⋏ q ⟶ r ⋏ q := ⟨andReplaceLeft h.some⟩


def andReplaceRight' (hc : 𝓢 ⊢ p ⋏ q) (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋏ r := conj₃' (conj₁' hc) (h ⨀ conj₂' hc)
lemma andReplaceRight'! (hc : 𝓢 ⊢! p ⋏ q) (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋏ r := ⟨andReplaceRight' hc.some h.some⟩

def andReplaceRight (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋏ q ⟶ p ⋏ r := by
  apply deduct';
  exact andReplaceRight' (FiniteContext.id) (of h)
lemma andReplaceRight! (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋏ q ⟶ p ⋏ r := ⟨andReplaceRight h.some⟩


def andReplace' (hc : 𝓢 ⊢ p ⋏ q) (h₁ : 𝓢 ⊢ p ⟶ r) (h₂ : 𝓢 ⊢ q ⟶ s) : 𝓢 ⊢ r ⋏ s := andReplaceRight' (andReplaceLeft' hc h₁) h₂
lemma andReplace'! (hc : 𝓢 ⊢! p ⋏ q) (h₁ : 𝓢 ⊢! p ⟶ r) (h₂ : 𝓢 ⊢! q ⟶ s) : 𝓢 ⊢! r ⋏ s := ⟨andReplace' hc.some h₁.some h₂.some⟩

def andReplace (h₁ : 𝓢 ⊢ p ⟶ r) (h₂ : 𝓢 ⊢ q ⟶ s) : 𝓢 ⊢ p ⋏ q ⟶ r ⋏ s := by
  apply deduct';
  exact andReplace' FiniteContext.id (of h₁) (of h₂)
lemma andReplace! (h₁ : 𝓢 ⊢! p ⟶ r) (h₂ : 𝓢 ⊢! q ⟶ s) : 𝓢 ⊢! p ⋏ q ⟶ r ⋏ s := ⟨andReplace h₁.some h₂.some⟩


def orReplaceLeft' (hc : 𝓢 ⊢ p ⋎ q) (hp : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ r ⋎ q := disj₃' (impTrans hp disj₁) (disj₂) hc
lemma or_replace_left'! (hc : 𝓢 ⊢! p ⋎ q) (hp : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! r ⋎ q := ⟨orReplaceLeft' hc.some hp.some⟩

def orReplaceLeft (hp : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⋎ q ⟶ r ⋎ q := by
  apply deduct';
  exact orReplaceLeft' FiniteContext.id (of hp)
lemma or_replace_left! (hp : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⋎ q ⟶ r ⋎ q := ⟨orReplaceLeft hp.some⟩


def orReplaceRight' (hc : 𝓢 ⊢ p ⋎ q) (hq : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋎ r := disj₃' (disj₁) (impTrans hq disj₂) hc
lemma or_replace_right'! (hc : 𝓢 ⊢! p ⋎ q) (hq : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋎ r := ⟨orReplaceRight' hc.some hq.some⟩

def orReplaceRight (hq : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ p ⋎ q ⟶ p ⋎ r := by
  apply deduct';
  exact orReplaceRight' FiniteContext.id (of hq)
lemma or_replace_right! (hq : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! p ⋎ q ⟶ p ⋎ r := ⟨orReplaceRight hq.some⟩


def orReplace' (h : 𝓢 ⊢ p₁ ⋎ q₁) (hp : 𝓢 ⊢ p₁ ⟶ p₂) (hq : 𝓢 ⊢ q₁ ⟶ q₂) : 𝓢 ⊢ p₂ ⋎ q₂ := orReplaceRight' (orReplaceLeft' h hp) hq
lemma or_replace'! (h : 𝓢 ⊢! p₁ ⋎ q₁) (hp : 𝓢 ⊢! p₁ ⟶ p₂) (hq : 𝓢 ⊢! q₁ ⟶ q₂) : 𝓢 ⊢! p₂ ⋎ q₂ := ⟨orReplace' h.some hp.some hq.some⟩

def orReplace (hp : 𝓢 ⊢ p₁ ⟶ p₂) (hq : 𝓢 ⊢ q₁ ⟶ q₂) : 𝓢 ⊢ p₁ ⋎ q₁ ⟶ p₂ ⋎ q₂ := by
  apply deduct';
  exact orReplace' FiniteContext.id (of hp) (of hq) ;
lemma or_replace! (hp : 𝓢 ⊢! p₁ ⟶ p₂) (hq : 𝓢 ⊢! q₁ ⟶ q₂) : 𝓢 ⊢! p₁ ⋎ q₁ ⟶ p₂ ⋎ q₂ := ⟨orReplace hp.some hq.some⟩


def orReplaceIff (hp : 𝓢 ⊢ p₁ ⟷ p₂) (hq : 𝓢 ⊢ q₁ ⟷ q₂) : 𝓢 ⊢ p₁ ⋎ q₁ ⟷ p₂ ⋎ q₂ := by
  apply iffIntro;
  . exact orReplace (conj₁' hp) (conj₁' hq);
  . exact orReplace (conj₂' hp) (conj₂' hq);
lemma or_replace_iff! (hp : 𝓢 ⊢! p₁ ⟷ p₂) (hq : 𝓢 ⊢! q₁ ⟷ q₂) : 𝓢 ⊢! p₁ ⋎ q₁ ⟷ p₂ ⋎ q₂ := ⟨orReplaceIff hp.some hq.some⟩


def andReplaceIff (hp : 𝓢 ⊢ p₁ ⟷ p₂) (hq : 𝓢 ⊢ q₁ ⟷ q₂) : 𝓢 ⊢ p₁ ⋏ q₁ ⟷ p₂ ⋏ q₂ := by
  apply iffIntro;
  . exact andReplace (conj₁' hp) (conj₁' hq);
  . exact andReplace (conj₂' hp) (conj₂' hq);
lemma and_replace_iff! (hp : 𝓢 ⊢! p₁ ⟷ p₂) (hq : 𝓢 ⊢! q₁ ⟷ q₂) : 𝓢 ⊢! p₁ ⋏ q₁ ⟷ p₂ ⋏ q₂ := ⟨andReplaceIff hp.some hq.some⟩


def impReplaceIff (hp : 𝓢 ⊢ p₁ ⟷ p₂) (hq : 𝓢 ⊢ q₁ ⟷ q₂) : 𝓢 ⊢ (p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂) := by
  apply iffIntro;
  . apply deduct'; exact impTrans (of $ conj₂' hp) $ impTrans (FiniteContext.id) (of $ conj₁' hq);
  . apply deduct'; exact impTrans (of $ conj₁' hp) $ impTrans (FiniteContext.id) (of $ conj₂' hq);
lemma imp_replace_iff! (hp : 𝓢 ⊢! p₁ ⟷ p₂) (hq : 𝓢 ⊢! q₁ ⟷ q₂) : 𝓢 ⊢! (p₁ ⟶ q₁) ⟷ (p₂ ⟶ q₂) := ⟨impReplaceIff hp.some hq.some⟩


variable [System.NegationEquiv 𝓢]

def dni : 𝓢 ⊢ p ⟶ ~~p := by
  apply deduct';
  apply neg_equiv'.mpr;
  apply deduct;
  exact bot_of_mem_either (p := p) (by simp) (by simp);
@[simp] lemma dni! : 𝓢 ⊢! p ⟶ ~~p := ⟨dni⟩

def dni' (b : 𝓢 ⊢ p) : 𝓢 ⊢ ~~p := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! p) : 𝓢 ⊢! ~~p := ⟨dni' b.some⟩


def dniOr' (d : 𝓢 ⊢ p ⋎ q) : 𝓢 ⊢ ~~p ⋎ ~~q := disj₃' (impTrans dni disj₁) (impTrans dni disj₂) d
@[simp] lemma dniOr'! (d : 𝓢 ⊢! p ⋎ q) : 𝓢 ⊢! ~~p ⋎ ~~q := ⟨dniOr' d.some⟩

def dniAnd' (d : 𝓢 ⊢ p ⋏ q) : 𝓢 ⊢ ~~p ⋏ ~~q := conj₃' (dni' $ conj₁' d) (dni' $ conj₂' d)
@[simp] lemma dniAnd'! (d : 𝓢 ⊢! p ⋏ q) : 𝓢 ⊢! ~~p ⋏ ~~q := ⟨dniAnd' d.some⟩


def dn [HasDNE 𝓢] : 𝓢 ⊢ p ⟷ ~~p := iffIntro dni dne
@[simp] lemma dn! [HasDNE 𝓢] : 𝓢 ⊢! p ⟷ ~~p := ⟨dn⟩


def contra₀ : 𝓢 ⊢ (p ⟶ q) ⟶ (~q ⟶ ~p) := by
  apply deduct';
  apply deduct;
  apply neg_equiv'.mpr;
  apply deduct;
  have dp  : [p, ~q, p ⟶ q] ⊢[𝓢] p := FiniteContext.byAxm;
  have dpq : [p, ~q, p ⟶ q] ⊢[𝓢] p ⟶ q := FiniteContext.byAxm;
  have dq  : [p, ~q, p ⟶ q] ⊢[𝓢] q := dpq ⨀ dp;
  have dnq : [p, ~q, p ⟶ q] ⊢[𝓢] q ⟶ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm;
  exact dnq ⨀ dq;
@[simp] def contra₀! : 𝓢 ⊢! (p ⟶ q) ⟶ (~q ⟶ ~p) := ⟨contra₀⟩

def contra₀' (b : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~q ⟶ ~p := contra₀ ⨀ b
lemma contra₀'! (b : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~q ⟶ ~p := ⟨contra₀' b.some⟩


def contra₀x2' (b : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~~p ⟶ ~~q := contra₀' $ contra₀' b
lemma contra₀x2'! (b : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~~p ⟶ ~~q := ⟨contra₀x2' b.some⟩

def contra₀x2 : 𝓢 ⊢ (p ⟶ q) ⟶ (~~p ⟶ ~~q) := deduct' $ contra₀x2' FiniteContext.id
@[simp] lemma contra₀x2! : 𝓢 ⊢! (p ⟶ q) ⟶ (~~p ⟶ ~~q) := ⟨contra₀x2⟩


def contra₁' (b : 𝓢 ⊢ p ⟶ ~q) : 𝓢 ⊢ q ⟶ ~p := impTrans dni (contra₀' b)
lemma contra₁'! (b : 𝓢 ⊢! p ⟶ ~q) : 𝓢 ⊢! q ⟶ ~p := ⟨contra₁' b.some⟩

def contra₁ : 𝓢 ⊢ (p ⟶ ~q) ⟶ (q ⟶ ~p) := deduct' $ contra₁' FiniteContext.id
lemma contra₁! : 𝓢 ⊢! (p ⟶ ~q) ⟶ (q ⟶ ~p) := ⟨contra₁⟩


def contra₂' [HasDNE 𝓢] (b : 𝓢 ⊢ ~p ⟶ q) : 𝓢 ⊢ ~q ⟶ p := impTrans (contra₀' b) dne
lemma contra₂'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~p ⟶ q) : 𝓢 ⊢! ~q ⟶ p := ⟨contra₂' b.some⟩

def contra₂ [HasDNE 𝓢] : 𝓢 ⊢ (~p ⟶ q) ⟶ (~q ⟶ p) := deduct' $ contra₂' FiniteContext.id
@[simp] lemma contra₂! [HasDNE 𝓢] : 𝓢 ⊢! (~p ⟶ q) ⟶ (~q ⟶ p) := ⟨contra₂⟩


def contra₃' [HasDNE 𝓢] (b : 𝓢 ⊢ ~p ⟶ ~q) : 𝓢 ⊢ q ⟶ p := impTrans dni (contra₂' b)
lemma contra₃'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~p ⟶ ~q) : 𝓢 ⊢! q ⟶ p := ⟨contra₃' b.some⟩

def contra₃ [HasDNE 𝓢] : 𝓢 ⊢ (~p ⟶ ~q) ⟶ (q ⟶ p) :=  deduct' $ contra₃' FiniteContext.id
@[simp] lemma contra₃! [HasDNE 𝓢] : 𝓢 ⊢! (~p ⟶ ~q) ⟶ (q ⟶ p) := ⟨contra₃⟩


def neg_iff' (b : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ ~p ⟷ ~q := iffIntro (contra₀' $ conj₂' b) (contra₀' $ conj₁' b)
lemma neg_iff'! (b : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ~p ⟷ ~q := ⟨neg_iff' b.some⟩


def tne : 𝓢 ⊢ ~(~~p) ⟶ ~p := contra₀' dni
@[simp] lemma tne! : 𝓢 ⊢! ~(~~p) ⟶ ~p := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ~(~~p)) : 𝓢 ⊢ ~p := tne ⨀ b
lemma tne'! (b : 𝓢 ⊢! ~(~~p)) : 𝓢 ⊢! ~p := ⟨tne' b.some⟩

def implyLeftReplace (h : 𝓢 ⊢ q ⟶ p) : 𝓢 ⊢ (p ⟶ r) ⟶ (q ⟶ r) := by
  apply deduct';
  exact impTrans (of h) id;
lemma imply_left_replace! (h : 𝓢 ⊢! q ⟶ p) : 𝓢 ⊢! (p ⟶ r) ⟶ (q ⟶ r) := ⟨implyLeftReplace h.some⟩


lemma implyLeftReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! p ⟶ r ↔ 𝓢 ⊢! q ⟶ r := by
  constructor;
  . exact imp_trans! $ conj₂'! h;
  . exact imp_trans! $ conj₁'! h;


lemma implyRightReplaceIff'! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! r ⟶ p ↔ 𝓢 ⊢! r ⟶ q := by
  constructor;
  . intro hrp; exact imp_trans! hrp $ conj₁'! h;
  . intro hrq; exact imp_trans! hrq $ conj₂'! h;


def impSwap' (h : 𝓢 ⊢ p ⟶ q ⟶ r) : 𝓢 ⊢ q ⟶ p ⟶ r := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [p, q]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm;
lemma imp_swap'! (h : 𝓢 ⊢! (p ⟶ q ⟶ r)) : 𝓢 ⊢! (q ⟶ p ⟶ r) := ⟨impSwap' h.some⟩

def impSwap : 𝓢 ⊢ (p ⟶ q ⟶ r) ⟶ (q ⟶ p ⟶ r) := deduct' $ impSwap' FiniteContext.id
@[simp] lemma imp_swap! : 𝓢 ⊢! (p ⟶ q ⟶ r) ⟶ (q ⟶ p ⟶ r) := ⟨impSwap⟩


-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnDistributeImply : 𝓢 ⊢ ~~(p ⟶ q) ⟶ (~~p ⟶ ~~q) := by
  apply impSwap';
  apply deduct';
  exact impTrans (contra₀x2' $ deductInv $ of $ impSwap' $ contra₀x2) tne;
@[simp] lemma dn_distribute_imply! : 𝓢 ⊢! ~~(p ⟶ q) ⟶ (~~p ⟶ ~~q) := ⟨dnDistributeImply⟩

noncomputable def dnDistributeImply' (b : 𝓢 ⊢ ~~(p ⟶ q)) : 𝓢 ⊢ ~~p ⟶ ~~q := dnDistributeImply ⨀ b
lemma dn_distribute_imply'! (b : 𝓢 ⊢! ~~(p ⟶ q)) : 𝓢 ⊢! ~~p ⟶ ~~q := ⟨dnDistributeImply' b.some⟩


def introFalsumOfAnd' (h : 𝓢 ⊢ p ⋏ ~p) : 𝓢 ⊢ ⊥ := (neg_equiv'.mp $ conj₂' h) ⨀ (conj₁' h)
lemma introFalsumOfAnd'! (h : 𝓢 ⊢! p ⋏ ~p) : 𝓢 ⊢! ⊥ := ⟨introFalsumOfAnd' h.some⟩

def introFalsumOfAnd : 𝓢 ⊢ p ⋏ ~p ⟶ ⊥ := by
  apply deduct';
  exact introFalsumOfAnd' (p := p) $ FiniteContext.id
@[simp] lemma introFalsumOfAnd! : 𝓢 ⊢! p ⋏ ~p ⟶ ⊥ := ⟨introFalsumOfAnd⟩



def implyOfNotOr [HasEFQ 𝓢] : 𝓢 ⊢ (~p ⋎ q) ⟶ (p ⟶ q) := disj₃'' (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (p := p) (by simp) (by simp)
  ) imply₁
@[simp] lemma implyOfNotOr! [HasEFQ 𝓢] : 𝓢 ⊢! (~p ⋎ q) ⟶ (p ⟶ q) := ⟨implyOfNotOr⟩

def implyOfNotOr' [HasEFQ 𝓢] (b : 𝓢 ⊢ ~p ⋎ q) : 𝓢 ⊢ p ⟶ q := implyOfNotOr ⨀ b
lemma implyOfNotOr'! [HasEFQ 𝓢] (b : 𝓢 ⊢! ~p ⋎ q) : 𝓢 ⊢! p ⟶ q := ⟨implyOfNotOr' b.some⟩


def demorgan₁ : 𝓢 ⊢ (~p ⋎ ~q) ⟶ ~(p ⋏ q) := disj₃'' (contra₀' conj₁) (contra₀' conj₂)
@[simp] lemma demorgan₁! : 𝓢 ⊢! (~p ⋎ ~q) ⟶ ~(p ⋏ q) := ⟨demorgan₁⟩

def demorgan₁' (d : 𝓢 ⊢ ~p ⋎ ~q) : 𝓢 ⊢ ~(p ⋏ q)  := demorgan₁ ⨀ d
lemma demorgan₁'! (d : 𝓢 ⊢! ~p ⋎ ~q) : 𝓢 ⊢! ~(p ⋏ q) := ⟨demorgan₁' d.some⟩


def demorgan₂ : 𝓢 ⊢ (~p ⋏ ~q) ⟶ ~(p ⋎ q) := by
  apply andImplyIffImplyImply'.mpr;
  apply deduct';
  apply deduct;
  apply neg_equiv'.mpr;
  apply deduct;
  exact disj₃' (neg_equiv'.mp FiniteContext.byAxm) (neg_equiv'.mp FiniteContext.byAxm) (FiniteContext.byAxm (p := p ⋎ q));
@[simp] lemma demorgan₂! : 𝓢 ⊢! ~p ⋏ ~q ⟶ ~(p ⋎ q) := ⟨demorgan₂⟩

def demorgan₂' (d : 𝓢 ⊢ ~p ⋏ ~q) : 𝓢 ⊢ ~(p ⋎ q) := demorgan₂ ⨀ d
lemma demorgan₂'! (d : 𝓢 ⊢! ~p ⋏ ~q) : 𝓢 ⊢! ~(p ⋎ q) := ⟨demorgan₂' d.some⟩


def demorgan₃ : 𝓢 ⊢ ~(p ⋎ q) ⟶ (~p ⋏ ~q) := by
  apply deduct';
  exact conj₃' (deductInv $ contra₀' $ disj₁) (deductInv $ contra₀' $ disj₂)
@[simp] lemma demorgan₃! : 𝓢 ⊢! ~(p ⋎ q) ⟶ (~p ⋏ ~q) := ⟨demorgan₃⟩

def demorgan₃' (b : 𝓢 ⊢ ~(p ⋎ q)) : 𝓢 ⊢ ~p ⋏ ~q := demorgan₃ ⨀ b
lemma demorgan₃'! (b : 𝓢 ⊢! ~(p ⋎ q)) : 𝓢 ⊢! ~p ⋏ ~q := ⟨demorgan₃' b.some⟩


-- TODO: Actually this can be computable but it's too slow.
noncomputable def demorgan₄ [HasDNE 𝓢] : 𝓢 ⊢ ~(p ⋏ q) ⟶ (~p ⋎ ~q) := by
  apply contra₂';
  apply deduct';
  exact andReplace' (demorgan₃' $ FiniteContext.id) dne dne;
@[simp] lemma demorgan₄! [HasDNE 𝓢] : 𝓢 ⊢! ~(p ⋏ q) ⟶ (~p ⋎ ~q) := ⟨demorgan₄⟩

noncomputable def demorgan₄' [HasDNE 𝓢] (b : 𝓢 ⊢ ~(p ⋏ q)) : 𝓢 ⊢ ~p ⋎ ~q := demorgan₄ ⨀ b
lemma demorgan₄'! [HasDNE 𝓢] (b : 𝓢 ⊢! ~(p ⋏ q)) : 𝓢 ⊢! ~p ⋎ ~q := ⟨demorgan₄' b.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def NotOrOfImply' [HasDNE 𝓢] (d : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ ~p ⋎ q := by
  apply dne';
  apply neg_equiv'.mpr;
  apply deduct';
  have d₁ : [~(~p ⋎ q)] ⊢[𝓢] ~~p ⋏ ~q := demorgan₃' $ FiniteContext.id;
  have d₂ : [~(~p ⋎ q)] ⊢[𝓢] ~p ⟶ ⊥ := neg_equiv'.mp $ conj₁' d₁;
  have d₃ : [~(~p ⋎ q)] ⊢[𝓢] ~p := (of (Γ := [~(~p ⋎ q)]) $ contra₀' d) ⨀ (conj₂' d₁);
  exact d₂ ⨀ d₃;
lemma NotOrOfImply'! [HasDNE 𝓢] (d : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! ~p ⋎ q := ⟨NotOrOfImply' d.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnCollectImply [HasEFQ 𝓢] : 𝓢 ⊢ (~~p ⟶ ~~q) ⟶ ~~(p ⟶ q) := by
  apply deduct';
  apply neg_equiv'.mpr;
  exact impTrans
    (by
      apply deductInv;
      apply andImplyIffImplyImply'.mp;
      apply deduct;
      have d₁ : [(~~p ⟶ ~~q) ⋏ ~(p ⟶ q)] ⊢[𝓢] ~~p ⟶ ~~q := conj₁' (q := ~(p ⟶ q)) $ FiniteContext.id;
      have d₂ : [(~~p ⟶ ~~q) ⋏ ~(p ⟶ q)] ⊢[𝓢] ~~p ⋏ ~q := demorgan₃' $ (contra₀' implyOfNotOr) ⨀ (conj₂' (p := (~~p ⟶ ~~q)) $ FiniteContext.id)
      exact conj₃' (conj₂' d₂) (d₁ ⨀ (conj₁' d₂))
    )
    (introFalsumOfAnd (p := ~q));

@[simp] lemma dn_collect_imply! [HasEFQ 𝓢] : 𝓢 ⊢! (~~p ⟶ ~~q) ⟶ ~~(p ⟶ q) := ⟨dnCollectImply⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnCollectImply' [HasEFQ 𝓢] (b : 𝓢 ⊢ ~~p ⟶ ~~q) : 𝓢 ⊢ ~~(p ⟶ q) := dnCollectImply ⨀ b
lemma dn_collect_imply'! [HasEFQ 𝓢] (b : 𝓢 ⊢! ~~p ⟶ ~~q) : 𝓢 ⊢! ~~(p ⟶ q) := ⟨dnCollectImply' b.some⟩


def andImplyAndOfImply {p q p' q' : F} (bp : 𝓢 ⊢ p ⟶ p') (bq : 𝓢 ⊢ q ⟶ q') : 𝓢 ⊢ p ⋏ q ⟶ p' ⋏ q' :=
  deduct' <| andIntro
    (deductInv' <| impTrans conj₁ bp)
    (deductInv' <| impTrans conj₂ bq)

def andIffAndOfIff {p q p' q' : F} (bp : 𝓢 ⊢ p ⟷ p') (bq : 𝓢 ⊢ q ⟷ q') : 𝓢 ⊢ p ⋏ q ⟷ p' ⋏ q' :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp) (andRight bq))

def conj'IffConj : (Γ : List F) → 𝓢 ⊢ Γ.conj' ⟷ Γ.conj
  | []          => iffId ⊤
  | [_]         => iffIntro (deduct' <| andIntro FiniteContext.id verum) conj₁
  | p :: q :: Γ => andIffAndOfIff (iffId p) (conj'IffConj (q :: Γ))
@[simp] lemma conj'IffConj! : 𝓢 ⊢! Γ.conj' ⟷ Γ.conj := ⟨conj'IffConj Γ⟩


lemma implyLeft_conj_eq_conj'! : 𝓢 ⊢! Γ.conj ⟶ p ↔ 𝓢 ⊢! Γ.conj' ⟶ p := implyLeftReplaceIff'! $ iffComm'! conj'IffConj!


lemma generalConj'! (h : p ∈ Γ) : 𝓢 ⊢! Γ.conj' ⟶ p := implyLeftReplaceIff'! conj'IffConj! |>.mpr (generalConj! h)
lemma generalConj'₂! (h : p ∈ Γ) (d : 𝓢 ⊢! Γ.conj') : 𝓢 ⊢! p := (generalConj'! h) ⨀ d

namespace FiniteContext

def ofDef' {Γ : List F} {p : F} (b : 𝓢 ⊢ Γ.conj' ⟶ p) : Γ ⊢[𝓢] p := ofDef <| impTrans (andRight <| conj'IffConj Γ) b
def ofDef'! (b : 𝓢 ⊢! Γ.conj' ⟶ p) : Γ ⊢[𝓢]! p := ⟨ofDef' b.some⟩

def toDef' {Γ : List F} {p : F} (b : Γ ⊢[𝓢] p) : 𝓢 ⊢ Γ.conj' ⟶ p := impTrans (andLeft <| conj'IffConj Γ) (toDef b)
def toDef'! (b : Γ ⊢[𝓢]! p) : 𝓢 ⊢! Γ.conj' ⟶ p := ⟨toDef' b.some⟩

lemma provable_iff' {p : F} : Γ ⊢[𝓢]! p ↔ 𝓢 ⊢! Γ.conj' ⟶ p := ⟨fun h ↦ ⟨toDef' h.get⟩, fun h ↦ ⟨ofDef' h.get⟩⟩

end FiniteContext



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

lemma conj'conj'_subset (h : ∀ p, p ∈ Γ → p ∈ Δ) : 𝓢 ⊢! Δ.conj' ⟶ Γ.conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using dhyp! verum!;
  | hsingle => simp_all; exact generalConj'! h;
  | hcons p Γ hne ih => simp_all; exact implyRightAnd! (generalConj'! h.1) ih;

def implyOrLeft' (h : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ (r ⋎ q) := by
  apply deduct';
  apply disj₁';
  apply deductInv;
  exact of h;

lemma implyOrLeft'! (h : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ (r ⋎ q) := ⟨implyOrLeft' h.some⟩

def implyOrRight' (h : 𝓢 ⊢ q ⟶ r) : 𝓢 ⊢ q ⟶ (p ⋎ r) := by
  apply deduct';
  apply disj₂';
  apply deductInv;
  exact of h;

lemma implyOrRight'! (h : 𝓢 ⊢! q ⟶ r) : 𝓢 ⊢! q ⟶ (p ⋎ r) := ⟨implyOrRight' h.some⟩

lemma or_assoc'! : 𝓢 ⊢! p ⋎ (q ⋎ r) ↔ 𝓢 ⊢! (p ⋎ q) ⋎ r := by
  constructor;
  . intro h;
    exact disj₃'!
      (implyOrLeft'! $ implyOrLeft'! imp_id!)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact disj₃'! (implyOrLeft'! $ implyOrRight'! imp_id!) (implyOrRight'! imp_id!) id!;
      )
      h;
  . intro h;
    exact disj₃'!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact disj₃'! (implyOrLeft'! imp_id!) (implyOrRight'! $ implyOrLeft'! imp_id!) id!;
      )
      (implyOrRight'! $ implyOrRight'! imp_id!)
      h;

lemma and_assoc! : 𝓢 ⊢! (p ⋏ q) ⋏ r ⟷ p ⋏ (q ⋏ r) := by
  apply iff_intro!;
  . apply FiniteContext.deduct'!;
    have hp : [(p ⋏ q) ⋏ r] ⊢[𝓢]! p := conj₁'! $ conj₁'! id!;
    have hq : [(p ⋏ q) ⋏ r] ⊢[𝓢]! q := conj₂'! $ conj₁'! id!;
    have hr : [(p ⋏ q) ⋏ r] ⊢[𝓢]! r := conj₂'! id!;
    exact conj₃'! hp (conj₃'! hq hr);
  . apply FiniteContext.deduct'!;
    have hp : [p ⋏ (q ⋏ r)] ⊢[𝓢]! p := conj₁'! id!;
    have hq : [p ⋏ (q ⋏ r)] ⊢[𝓢]! q := conj₁'! $ conj₂'! id!;
    have hr : [p ⋏ (q ⋏ r)] ⊢[𝓢]! r := conj₂'! $ conj₂'! id!;
    apply conj₃'!;
    . exact conj₃'! hp hq;
    . exact hr;

lemma cut! (d₁ : 𝓢 ⊢! p₁ ⋏ c ⟶ q₁) (d₂ : 𝓢 ⊢! p₂ ⟶ c ⋎ q₂) : 𝓢 ⊢! p₁ ⋏ p₂ ⟶ q₁ ⋎ q₂ := by
  apply deduct'!;
  exact disj₃'! (implyOrLeft'! $ of'! (andImplyIffImplyImply'!.mp d₁) ⨀ (conj₁'! id!)) disj₂! (of'! d₂ ⨀ conj₂'! id!);

lemma imply_left_and_comm'! (d : 𝓢 ⊢! p ⋏ q ⟶ r) : 𝓢 ⊢! q ⋏ p ⟶ r := imp_trans! andComm! d

lemma id_conj'! (he : ∀ g ∈ Γ, g = p) : 𝓢 ⊢! p ⟶ Γ.conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp_all only [List.conj'_nil, IsEmpty.forall_iff, forall_const]; exact dhyp! $ verum!;
  | hsingle => simp_all only [List.mem_singleton, forall_eq, List.conj'_singleton, imp_id!];
  | hcons r Γ h ih =>
    simp [List.conj'_cons_nonempty h];
    simp at he;
    have ⟨he₁, he₂⟩ := he;
    subst he₁;
    exact implyRightAnd! imp_id! (ih he₂);

lemma replace_imply_left_conj'! (he : ∀ g ∈ Γ, g = p) (hd : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! p ⟶ q := imp_trans! (id_conj'! he) hd

lemma implyLeft_cons_conj'! : 𝓢 ⊢! (p :: Γ).conj' ⟶ q ↔ 𝓢 ⊢! p ⋏ Γ.conj' ⟶ q := by
  induction Γ with
  | nil =>
    simp [andImplyIffImplyImply'!];
    constructor;
    . intro h; apply imp_swap'!; exact dhyp! h;
    . intro h; exact imp_swap'! h ⨀ verum!;
  | cons q ih => simp;

lemma imply_left_concat_conj'! : 𝓢 ⊢! (Γ ++ Δ).conj' ⟶ Γ.conj' ⋏ Δ.conj' := by
  apply FiniteContext.deduct'!;
  have : [(Γ ++ Δ).conj'] ⊢[𝓢]! (Γ ++ Δ).conj' := id!;
  have d := iff_provable_list_conj.mp this;
  apply conj₃'!;
  . apply iff_provable_list_conj.mpr;
    intro p hp;
    exact d p (by simp; left; exact hp);
  . apply iff_provable_list_conj.mpr;
    intro p hp;
    exact d p (by simp; right; exact hp);

@[simp]
lemma forthbackConjRemove : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ Γ.conj' := by
  apply deduct'!;
  apply iff_provable_list_conj.mpr;
  intro q hq;
  by_cases e : q = p;
  . subst e; exact conj₂'! id!;
  . exact iff_provable_list_conj.mp (conj₁'! id!) q (by apply List.mem_remove_iff.mpr; simp_all);

lemma implyLeftRemoveConj' (b : 𝓢 ⊢! Γ.conj' ⟶ q) : 𝓢 ⊢! (Γ.remove p).conj' ⋏ p ⟶ q := imp_trans! forthbackConjRemove b

lemma iff_concat_conj'! : 𝓢 ⊢! (Γ ++ Δ).conj' ↔ 𝓢 ⊢! Γ.conj' ⋏ Δ.conj' := by
  constructor;
  . intro h;
    replace h := iff_provable_list_conj.mp h;
    apply conj₃'!;
    . apply iff_provable_list_conj.mpr;
      intro p hp; exact h p (by simp only [List.mem_append]; left; simpa);
    . apply iff_provable_list_conj.mpr;
      intro p hp; exact h p (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply iff_provable_list_conj.mpr;
    simp only [List.mem_append];
    rintro p (hp₁ | hp₂);
    . exact (iff_provable_list_conj.mp $ conj₁'! h) p hp₁;
    . exact (iff_provable_list_conj.mp $ conj₂'! h) p hp₂;

lemma iff_concat_conj! : 𝓢 ⊢! (Γ ++ Δ).conj' ⟷ Γ.conj' ⋏ Δ.conj' := by
  apply iff_intro!;
  . apply deduct'!; apply iff_concat_conj'!.mp; exact id!;
  . apply deduct'!; apply iff_concat_conj'!.mpr; exact id!;

lemma or_assoc! : 𝓢 ⊢! p ⋎ (q ⋎ r) ⟷ (p ⋎ q) ⋎ r := by
  apply iff_intro!;
  . exact deduct'! $ or_assoc'!.mp id!;
  . exact deduct'! $ or_assoc'!.mpr id!;

lemma or_replace_right_iff! (d : 𝓢 ⊢! q ⟷ r) : 𝓢 ⊢! p ⋎ q ⟷ p ⋎ r := by
  apply iff_intro!;
  . apply or_replace_right!; exact conj₁'! d;
  . apply or_replace_right!; exact conj₂'! d;

lemma or_replace_left_iff! (d : 𝓢 ⊢! p ⟷ r) : 𝓢 ⊢! p ⋎ q ⟷ r ⋎ q := by
  apply iff_intro!;
  . apply or_replace_left!; exact conj₁'! d;
  . apply or_replace_left!; exact conj₂'! d;

lemma iff_concact_disj! [HasEFQ 𝓢] : 𝓢 ⊢! (Γ ++ Δ).disj' ⟷ Γ.disj' ⋎ Δ.disj' := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp only [List.append_nil, List.disj'_nil];
    apply iff_intro!;
    . simp;
    . exact disj₃''! efq! efq!;
  case hnil.hsingle =>
    simp only [List.nil_append, List.disj'_singleton, List.disj'_nil];
    apply iff_intro!;
    . simp;
    . exact disj₃''! efq! imp_id!;
  case hsingle.hnil =>
    simp only [List.singleton_append, List.disj'_singleton, List.disj'_nil];
    apply iff_intro!;
    . simp;
    . exact disj₃''! imp_id! efq!;
  case hcons.hnil =>
    simp only [List.append_nil, List.disj'_nil];
    apply iff_intro!;
    . simp;
    . exact disj₃''! imp_id! efq!;
  case hnil.hcons =>
    simp only [List.nil_append, List.disj'_nil];
    apply iff_intro!;
    . simp;
    . exact disj₃''! efq! imp_id!;
  case hsingle.hsingle => simp only [List.singleton_append, ne_eq, not_false_eq_true, List.disj'_cons_nonempty, List.disj'_singleton, iff_id!];
  case hsingle.hcons => simp only [List.singleton_append, ne_eq, not_false_eq_true, List.disj'_cons_nonempty, List.disj'_singleton, iff_id!];
  case hcons.hsingle p ps hps ihp q =>
    simp_all;
    apply iff_trans! (by
      apply or_replace_right_iff!;
      simpa using @ihp [q];
    ) or_assoc!;
  case hcons.hcons p ps hps ihp q qs hqs ihq =>
    simp_all only [ne_eq, List.cons_append, List.append_eq_nil, and_self, not_false_eq_true, List.disj'_cons_nonempty];
    apply iff_trans! (by
      apply or_replace_right_iff!;
      exact iff_trans! (@ihp (q :: qs)) (by
        apply or_replace_right_iff!;
        simp [List.disj'_cons_nonempty hqs];
      )
    ) or_assoc!;

lemma iff_concact_disj'! [HasEFQ 𝓢] : 𝓢 ⊢! (Γ ++ Δ).disj' ↔ 𝓢 ⊢! Γ.disj' ⋎ Δ.disj' := by
  constructor;
  . intro h; exact (conj₁'! iff_concact_disj!) ⨀ h;
  . intro h; exact (conj₂'! iff_concact_disj!) ⨀ h;

lemma implyRight_cons_disj'! [HasEFQ 𝓢] : 𝓢 ⊢! p ⟶ (q :: Γ).disj' ↔ 𝓢 ⊢! p ⟶ q ⋎ Γ.disj' := by
  induction Γ with
  | nil =>
    simp;
    constructor;
    . intro h; exact imp_trans! h disj₁!;
    . intro h; exact imp_trans! h $ disj₃''! imp_id! efq!;
  | cons q ih => simp;

@[simp]
lemma forthback_disj'_remove [HasEFQ 𝓢] : 𝓢 ⊢! Γ.disj' ⟶ p ⋎ (Γ.remove p).disj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle q =>
    simp;
    by_cases h: q = p;
    . subst_vars; simp;
    . simp [(List.remove_singleton_of_ne h)];
  | hcons q Γ h ih =>
    simp [(List.disj'_cons_nonempty h)];
    by_cases hpq : q = p;
    . simp_all only [ne_eq, List.remove_cons_self]; exact disj₃''! disj₁! ih;
    . simp_all [(List.remove_cons_of_ne Γ hpq)];
      by_cases hqΓ : Γ.remove p = [];
      . simp_all;
        exact disj₃''! disj₂! (imp_trans! ih $ or_replace_right! efq!);
      . simp [(List.disj'_cons_nonempty hqΓ)];
        exact disj₃''! (imp_trans! disj₁! disj₂!) (imp_trans! ih (or_replace_right! disj₂!));

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
    exact disj₃'! (by simp) (weakening! (by simp) $ provable_iff_provable.mp $ ih hd₂) id!

lemma disj_allsame'! [HasEFQ 𝓢] (hd : ∀ q ∈ Γ, q = p) (h : 𝓢 ⊢! Γ.disj') : 𝓢 ⊢! p := (disj_allsame! hd) ⨀ h

instance [HasDNE 𝓢] : HasEFQ 𝓢 where
  efq p := by
    apply contra₃';
    exact impTrans (conj₁' neg_equiv) $ impTrans (impSwap' imply₁) (conj₂' neg_equiv);

def dneOr [HasDNE 𝓢] (d : 𝓢 ⊢ ~~p ⋎ ~~q) : 𝓢 ⊢ p ⋎ q := disj₃' (impTrans dne disj₁) (impTrans dne disj₂) d

-- TODO: Actually this can be computable but it's too slow.
noncomputable instance [HasDNE 𝓢] : HasLEM 𝓢 where
  lem _ := dneOr $ NotOrOfImply' dni

instance [HasEFQ 𝓢] [HasLEM 𝓢] : HasDNE 𝓢 where
  dne p := by
    apply deduct';
    exact disj₃' (impId _) (by
      apply deduct;
      have nnp : [~p, ~~p] ⊢[𝓢] ~p ⟶ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm;
      have np : [~p, ~~p] ⊢[𝓢] ~p := FiniteContext.byAxm;
      exact efq' $ nnp ⨀ np;
    ) $ of lem;;

end LO.System

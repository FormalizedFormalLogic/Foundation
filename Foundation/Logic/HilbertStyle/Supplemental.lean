import Foundation.Logic.Entailment
import Foundation.Logic.HilbertStyle.Context
import Foundation.Vorspiel.List.Supplemental
import Foundation.Vorspiel.Finset.Supplemental

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

omit [DecidableEq F] in
@[simp] lemma CONV! : 𝓢 ⊢! ⊤ ➝ ∼⊥ := by
  apply FiniteContext.deduct'!;
  exact NO!;

def innerMDP : 𝓢 ⊢ φ ⋏ (φ ➝ ψ) ➝ ψ := by
  apply deduct';
  have hp  : [φ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have hpq : [φ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  exact hpq ⨀ hp;
lemma inner_mdp! : 𝓢 ⊢! φ ⋏ (φ ➝ ψ) ➝ ψ := ⟨innerMDP⟩

def bot_of_mem_either (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢] φ ➝ ⊥ := CO_of_N $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

@[simp] lemma bot_of_mem_either! (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩

def efq_of_mem_either [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ψ := of_O $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ψ := ⟨efq_of_mem_either h₁ h₂⟩

def CNC [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ∼φ ➝ φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma CNC! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ∼φ ➝ φ ➝ ψ := ⟨CNC⟩

def CCN [HasAxiomEFQ 𝓢] : 𝓢 ⊢ φ ➝ ∼φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma CCN! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ∼φ ➝ ψ := ⟨CCN⟩

lemma C_of_N [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! φ ➝ ψ := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [φ] ⊢[𝓢]! φ ➝ ⊥ := of'! $ N!_iff_CO!.mp h;
  exact of_O! (dnp ⨀ FiniteContext.id!);

lemma CN!_of_! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼φ ➝ ψ := CCN! ⨀ h

def negMDP (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (CO_of_N hnp) ⨀ hn
-- infixl:90 "⨀" => negMDP

omit [DecidableEq F] in lemma neg_mdp (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := ⟨negMDP hnp.some hn.some⟩
-- infixl:90 "⨀" => neg_mdp

def A_of_ANNNN [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := of_C_of_C_of_A (C_trans dne or₁) (C_trans dne or₂) d
omit [DecidableEq F] in lemma A!_of_ANNNN! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨A_of_ANNNN d.some⟩

def right_A_intro_left (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ (χ ⋎ ψ) := by
  apply deduct';
  apply A_intro_left;
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma right_A!_intro_left (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ (χ ⋎ ψ) := ⟨right_A_intro_left h.some⟩

def right_A_intro_right (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ (φ ⋎ χ) := by
  apply deduct';
  apply A_intro_right;
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma right_A!_intro_right (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! ψ ➝ (φ ⋎ χ) := ⟨right_A_intro_right h.some⟩

omit [DecidableEq F] in
def right_K_intro (hq : 𝓢 ⊢ φ ➝ ψ) (hr : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢] φ ➝ ψ := of hq;
  replace hr : [] ⊢[𝓢] φ ➝ χ := of hr;
  exact K_intro (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
lemma right_K!_intro (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨right_K_intro hq.some hr.some⟩

omit [DecidableEq F] in lemma left_K!_symm (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! ψ ⋏ φ ➝ χ := C!_trans CKK! d

lemma left_K!_intro_right (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (ψ ⋏ φ) ➝ χ := by
  apply CK!_iff_CC!.mpr;
  apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;

lemma left_K!_intro_left (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (φ ⋏ ψ) ➝ χ := C!_trans CKK! (left_K!_intro_right h)

lemma cut! (d₁ : 𝓢 ⊢! φ₁ ⋏ c ➝ ψ₁) (d₂ : 𝓢 ⊢! φ₂ ➝ c ⋎ ψ₂) : 𝓢 ⊢! φ₁ ⋏ φ₂ ➝ ψ₁ ⋎ ψ₂ := by
  apply deduct'!;
  exact of_C!_of_C!_of_A! (right_A!_intro_left $ of'! (CK!_iff_CC!.mp d₁) ⨀ (K!_left id!)) or₂! (of'! d₂ ⨀ K!_right id!);


def inner_A_symm : 𝓢 ⊢ φ ⋎ ψ ➝ ψ ⋎ φ := by
  apply deduct';
  exact of_C_of_C_of_A or₂ or₁ $ FiniteContext.id
omit [DecidableEq F] in lemma or_comm! : 𝓢 ⊢! φ ⋎ ψ ➝ ψ ⋎ φ := ⟨inner_A_symm⟩

def A_symm (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := inner_A_symm ⨀ h
omit [DecidableEq F] in lemma or_comm'! (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := ⟨A_symm h.some⟩

omit [DecidableEq F] in
lemma A!_assoc : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢! (φ ⋎ ψ) ⋎ χ := by
  constructor;
  . intro h;
    exact of_C!_of_C!_of_A!
      (right_A!_intro_left $ right_A!_intro_left C!_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C!_of_C!_of_A! (right_A!_intro_left $ right_A!_intro_right C!_id) (right_A!_intro_right C!_id) id!;
      )
      h;
  . intro h;
    exact of_C!_of_C!_of_A!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C!_of_C!_of_A! (right_A!_intro_left C!_id) (right_A!_intro_right $ right_A!_intro_left C!_id) id!;
      )
      (right_A!_intro_right $ right_A!_intro_right C!_id)
      h;

omit [DecidableEq F] in
lemma K!_assoc : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply E!_intro;
  . apply FiniteContext.deduct'!;
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! φ := K!_left $ K!_left id!;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! ψ := K!_right $ K!_left id!;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! χ := K!_right id!;
    exact K!_intro hp (K!_intro hq hr);
  . apply FiniteContext.deduct'!;
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! φ := K!_left id!;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! ψ := K!_left $ K!_right id!;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! χ := K!_right $ K!_right id!;
    apply K!_intro;
    . exact K!_intro hp hq;
    . exact hr;

omit [DecidableEq F] in lemma K!_assoc_mp (h : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ) : 𝓢 ⊢! φ ⋏ (ψ ⋏ χ) := C_of_E_mp! K!_assoc ⨀ h
omit [DecidableEq F] in lemma K!_assoc_mpr (h : 𝓢 ⊢! φ ⋏ (ψ ⋏ χ)) : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ := C_of_E_mpr! K!_assoc ⨀ h

def K_replace_left (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋏ ψ := K_intro (h ⨀ K_left hc) (K_right hc)
omit [DecidableEq F] in lemma K!_replace_left (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋏ ψ := ⟨K_replace_left hc.some h.some⟩

def CKK_of_C (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ψ := by
  apply deduct';
  exact K_replace_left FiniteContext.id (of h)
omit [DecidableEq F] in lemma CKK!_of_C! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ψ := ⟨CKK_of_C h.some⟩


def K_replace_right (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ χ := K_intro (K_left hc) (h ⨀ K_right hc)
omit [DecidableEq F] in lemma K!_replace_right (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ χ := ⟨K_replace_right hc.some h.some⟩

def CKK_of_C' (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ φ ⋏ χ := by
  apply deduct';
  exact K_replace_right (FiniteContext.id) (of h)
omit [DecidableEq F] in lemma CKK!_of_C!' (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ φ ⋏ χ := ⟨CKK_of_C' h.some⟩


def K_replace (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ χ ⋏ ξ := K_replace_right (K_replace_left hc h₁) h₂
omit [DecidableEq F] in lemma K!_replace (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! χ ⋏ ξ := ⟨K_replace hc.some h₁.some h₂.some⟩

def CKK_of_C_of_C (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ξ := by
  apply deduct';
  exact K_replace FiniteContext.id (of h₁) (of h₂)
omit [DecidableEq F] in lemma CKK!_of_C!_of_C! (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ξ := ⟨CKK_of_C_of_C h₁.some h₂.some⟩


def A_replace_left (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋎ ψ := of_C_of_C_of_A (C_trans hp or₁) (or₂) hc
omit [DecidableEq F] in lemma A!_replace_left (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋎ ψ := ⟨A_replace_left hc.some hp.some⟩

def CAA_of_C_left (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ ⋎ ψ := by
  apply deduct';
  exact A_replace_left FiniteContext.id (of hp)
omit [DecidableEq F] in lemma or_replace_left! (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ ⋎ ψ := ⟨CAA_of_C_left hp.some⟩


def A_replace_right (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ χ := of_C_of_C_of_A (or₁) (C_trans hq or₂) hc
omit [DecidableEq F] in lemma A!_replace_right (hc : 𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ χ := ⟨A_replace_right hc.some hq.some⟩

def CAA_of_C_right (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ φ ⋎ χ := by
  apply deduct';
  exact A_replace_right FiniteContext.id (of hq)
omit [DecidableEq F] in lemma CAA!_of_C!_right (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ φ ⋎ χ := ⟨CAA_of_C_right hq.some⟩


def A_replace (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₂ ⋎ ψ₂ := A_replace_right (A_replace_left h hp) hq

omit [DecidableEq F] in lemma A!_replace (h : 𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ := ⟨A_replace h.some hp.some hq.some⟩

def CAA_of_C_of_C (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := by
  apply deduct';
  exact A_replace FiniteContext.id (of hp) (of hq) ;
omit [DecidableEq F] in lemma CAA!_of_C!_of_C! (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := ⟨CAA_of_C_of_C hp.some hq.some⟩

def EAA_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := by
  apply E_intro;
  . exact CAA_of_C_of_C (K_left hp) (K_left hq);
  . exact CAA_of_C_of_C (K_right hp) (K_right hq);
omit [DecidableEq F] in lemma EAA!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := ⟨EAA_of_E_of_E hp.some hq.some⟩

omit [DecidableEq F] in
lemma EAAAA! : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ⭤ (φ ⋎ ψ) ⋎ χ := by
  apply E!_intro;
  . exact deduct'! $ A!_assoc.mp id!;
  . exact deduct'! $ A!_assoc.mpr id!;

omit [DecidableEq F] in
lemma EAA!_of_E!_right (d : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ φ ⋎ χ := by
  apply E!_intro;
  . apply CAA!_of_C!_right; exact K!_left d;
  . apply CAA!_of_C!_right; exact K!_right d;

omit [DecidableEq F] in
lemma EAA!_of_E!_left (d : 𝓢 ⊢! φ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ χ ⋎ ψ := by
  apply E!_intro;
  . apply or_replace_left!; exact K!_left d;
  . apply or_replace_left!; exact K!_right d;


def EKK_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := by
  apply E_intro;
  . exact CKK_of_C_of_C (K_left hp) (K_left hq);
  . exact CKK_of_C_of_C (K_right hp) (K_right hq);
omit [DecidableEq F] in lemma EKK!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := ⟨EKK_of_E_of_E hp.some hq.some⟩


def ECC_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := by
  apply E_intro;
  . apply deduct'; exact C_trans (of $ K_right hp) $ C_trans (FiniteContext.id) (of $ K_left hq);
  . apply deduct'; exact C_trans (of $ K_left hp) $ C_trans (FiniteContext.id) (of $ K_right hq);
omit [DecidableEq F] in lemma ECC!_of_E!_of_E! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := ⟨ECC_of_E_of_E hp.some hq.some⟩

omit [DecidableEq F] in
lemma C!_repalce (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ➝ ψ₁ ↔ 𝓢 ⊢! φ₂ ➝ ψ₂ :=
  iff_of_E! (ECC!_of_E!_of_E! hp hq)

def dni : 𝓢 ⊢ φ ➝ ∼∼φ := by
  apply deduct';
  apply N_of_CO;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma dni! : 𝓢 ⊢! φ ➝ ∼∼φ := ⟨dni⟩

def dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := ⟨dni' b.some⟩


def ANNNN_of_A (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := of_C_of_C_of_A (C_trans dni or₁) (C_trans dni or₂) d
lemma ANNNN!_of_A! (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := ⟨ANNNN_of_A d.some⟩

def KNNNN_of_K (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := K_intro (dni' $ K_left d) (dni' $ K_right d)
lemma KNNNN!_of_K! (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := ⟨KNNNN_of_K d.some⟩

def CNNOO : 𝓢 ⊢ ∼∼⊥ ➝ ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ ➝ ⊥ := CO_of_N byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := N_of_CO (C_id ⊥)
  exact d₁ ⨀ d₂

def ENNOO : 𝓢 ⊢ ∼∼⊥ ⭤ ⊥ := K_intro CNNOO dni

def dn [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ∼∼φ := E_intro dni dne
@[simp] lemma dn! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ∼∼φ := ⟨dn⟩


def CCCNN : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := by
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  have dp  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ ➝ ⊥ := CO_of_N $ FiniteContext.byAxm;
  exact dnq ⨀ dq;
@[simp] def CCCNN! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := ⟨CCCNN⟩

@[deprecated "use `CCCNN`"] alias contra₀ := CCCNN
@[deprecated "use `CCCNN!`"] alias contra₀! := CCCNN!

def contra (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ ∼φ := CCCNN ⨀ b
lemma contra! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ ∼φ := ⟨contra b.some⟩

@[deprecated "use `contra`"] alias contra₀' := contra
@[deprecated "use `contra!`"] alias contra₀'! := contra!

def CNNNN_of_C (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := contra $ contra b
lemma CNNNN!_of_C! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨CNNNN_of_C b.some⟩

def CCCNNNN : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := deduct' $ CNNNN_of_C FiniteContext.id
@[simp] lemma CCCNNNN! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨CCCNNNN⟩


def CN_of_CN_right (b : 𝓢 ⊢ φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ ∼φ := C_trans dni (contra b)
lemma CN!_of_CN!_right (b : 𝓢 ⊢! φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ ∼φ := ⟨CN_of_CN_right b.some⟩

def CCNCN : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := deduct' $ CN_of_CN_right FiniteContext.id
lemma CCNCN! : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := ⟨CCNCN⟩


def CN_of_CN_left [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ φ := C_trans (contra b) dne
lemma CN!_of_CN!_left [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ φ := ⟨CN_of_CN_left b.some⟩

def CCNCN' [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := deduct' $ CN_of_CN_left FiniteContext.id
@[simp] lemma CCNCN'! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := ⟨CCNCN'⟩


def C_of_CNN [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ φ := C_trans dni (CN_of_CN_left b)
lemma C!_of_CNN! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ φ := ⟨C_of_CNN b.some⟩

def CCNNC [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) :=  deduct' $ C_of_CNN FiniteContext.id
@[simp] lemma CCNNC! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) := ⟨CCNNC⟩


def ENN_of_E (b : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ∼φ ⭤ ∼ψ := E_intro (contra $ K_right b) (contra $ K_left b)
lemma ENN!_of_E! (b : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ∼φ ⭤ ∼ψ := ⟨ENN_of_E b.some⟩


def EN_of_EN_right [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ φ ⭤ ∼ψ) : 𝓢 ⊢ ∼φ ⭤ ψ := by
  apply E_intro;
  . apply CN_of_CN_left $  K_right h;
  . apply CN_of_CN_right $  K_left h;
lemma EN!_of_EN!_right [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! φ ⭤ ∼ψ) : 𝓢 ⊢! ∼φ ⭤ ψ := ⟨EN_of_EN_right h.some⟩

def EN_of_EN_left [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼φ ⭤ ψ) : 𝓢 ⊢ φ ⭤ ∼ψ := E_symm $ EN_of_EN_right $ E_symm h
lemma EN!_of_EN!_left [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼φ ⭤ ψ) : 𝓢 ⊢! φ ⭤ ∼ψ := ⟨EN_of_EN_left h.some⟩

section NegationEquiv

variable [Entailment.NegationEquiv 𝓢]

def ENNCCOO : 𝓢 ⊢ ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := by
  apply E_intro;
  . exact C_trans (by apply contra; exact K_right negEquiv) (K_left negEquiv)
  . exact C_trans (K_right negEquiv) (by apply contra; exact K_left negEquiv)
@[simp] lemma ENNCCOO! : 𝓢 ⊢! ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨ENNCCOO⟩

def ECCOO [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := E_trans dn ENNCCOO
lemma ECCOO! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨ECCOO⟩

end NegationEquiv

def CCCOCOC [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := by
  refine C_trans ?_ elimContra;
  apply deduct';
  exact C_trans (C_trans (K_left negEquiv) FiniteContext.byAxm) (K_right negEquiv);
@[simp] lemma CCCOCOC! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := ⟨CCCOCOC⟩


def tne : 𝓢 ⊢ ∼(∼∼φ) ➝ ∼φ := contra dni
@[simp] lemma tne! : 𝓢 ⊢! ∼(∼∼φ) ➝ ∼φ := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := tne ⨀ b
lemma tne'! (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := ⟨tne' b.some⟩

def tneIff : 𝓢 ⊢ ∼∼∼φ ⭤ ∼φ := K_intro tne dni

def CCC_of_C_left (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := by
  apply deduct';
  exact C_trans (of h) id;
omit [DecidableEq F] in lemma CCC!_of_C!_left (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨CCC_of_C_left h.some⟩

@[deprecated "use `CCC_of_C_left`"] alias rev_dhyp_imp' := CCC_of_C_left
@[deprecated "use `CCC!_of_C!_left`"] alias rev_dhyp_imp'! := CCC!_of_C!_left

omit [DecidableEq F] in
lemma C!_iff_C!_of_iff_left (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ➝ χ ↔ 𝓢 ⊢! ψ ➝ χ := by
  constructor;
  . exact C!_trans $ K!_right h;
  . exact C!_trans $ K!_left h;

omit [DecidableEq F] in
lemma C!_iff_C!_of_iff_right (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! χ ➝ φ ↔ 𝓢 ⊢! χ ➝ ψ := by
  constructor;
  . intro hrp; exact C!_trans hrp $ K!_left h;
  . intro hrq; exact C!_trans hrq $ K!_right h;


def C_swap (h : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ φ ➝ χ := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm;
lemma C!_swap (h : 𝓢 ⊢! (φ ➝ ψ ➝ χ)) : 𝓢 ⊢! (ψ ➝ φ ➝ χ) := ⟨C_swap h.some⟩

def CCCCC : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := deduct' $ C_swap FiniteContext.id
@[simp] lemma CCCCC! : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := ⟨CCCCC⟩

def C_of_CC (h : 𝓢 ⊢ φ ➝ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ψ := by
  apply deduct';
  have := of (Γ := [φ]) h;
  exact this ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
lemma C!_of_CC! (h : 𝓢 ⊢! φ ➝ φ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := ⟨C_of_CC h.some⟩

def CCC : 𝓢 ⊢ φ ➝ (φ ➝ ψ) ➝ ψ := C_swap $ C_id _
lemma CCC! : 𝓢 ⊢! φ ➝ (φ ➝ ψ) ➝ ψ := ⟨CCC⟩

def CCC_of_C_right (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (χ ➝ φ) ➝ (χ ➝ ψ) := imply₂ ⨀ (C_of_conseq h)
omit [DecidableEq F] in lemma CCC!_of_C!_right (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! (χ ➝ φ) ➝ (χ ➝ ψ) := ⟨CCC_of_C_right h.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def CNNCCNNNN : 𝓢 ⊢ ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := by
  apply C_swap;
  apply deduct';
  exact C_trans (CNNNN_of_C $ deductInv $ of $ C_swap $ CCCNNNN) tne;
@[simp] lemma CNNCCNNNN! : 𝓢 ⊢! ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨CNNCCNNNN⟩

noncomputable def CNNNN_of_NNC (b : 𝓢 ⊢ ∼∼(φ ➝ ψ)) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := CNNCCNNNN ⨀ b
lemma CNNNN!_of_NNC! (b : 𝓢 ⊢! ∼∼(φ ➝ ψ)) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨CNNNN_of_NNC b.some⟩


def O_intro_of_KN (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (CO_of_N $ K_right h) ⨀ (K_left h)
omit [DecidableEq F] in lemma O!_intro_of_KN! (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := ⟨O_intro_of_KN h.some⟩
/-- Law of contradiction -/
alias lac'! := O!_intro_of_KN!

def CKNO : 𝓢 ⊢ φ ⋏ ∼φ ➝ ⊥ := by
  apply deduct';
  exact O_intro_of_KN (φ := φ) $ FiniteContext.id
omit [DecidableEq F] in @[simp] lemma CKNO! : 𝓢 ⊢! φ ⋏ ∼φ ➝ ⊥ := ⟨CKNO⟩
/-- Law of contradiction -/
alias lac! := CKNO!

def CANC [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := left_A_intro (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (φ := φ) (by simp) (by simp)
  ) imply₁
@[simp] lemma CANC! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := ⟨CANC⟩

def C_of_AN [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼φ ⋎ ψ) : 𝓢 ⊢ φ ➝ ψ := CANC ⨀ b
lemma C!_of_AN! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼φ ⋎ ψ) : 𝓢 ⊢! φ ➝ ψ := ⟨C_of_AN b.some⟩


def CANNNK : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := left_A_intro (contra and₁) (contra and₂)
@[simp] lemma CANNNK! : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := ⟨CANNNK⟩

def NK_of_ANN (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ)  := CANNNK ⨀ d
lemma NK!_of_ANN! (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ) := ⟨NK_of_ANN d.some⟩


def CKNNNA : 𝓢 ⊢ (∼φ ⋏ ∼ψ) ➝ ∼(φ ⋎ ψ) := by
  apply CK_of_CC;
  apply deduct';
  apply deduct;
  apply N_of_CO;
  apply deduct;
  exact of_C_of_C_of_A (CO_of_N FiniteContext.byAxm) (CO_of_N FiniteContext.byAxm) (FiniteContext.byAxm (φ := φ ⋎ ψ));
@[simp] lemma CKNNNA! : 𝓢 ⊢! ∼φ ⋏ ∼ψ ➝ ∼(φ ⋎ ψ) := ⟨CKNNNA⟩

def NA_of_KNN (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := CKNNNA ⨀ d
lemma NA!_of_KNN! (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := ⟨NA_of_KNN d.some⟩


def CNAKNN : 𝓢 ⊢ ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact K_intro (deductInv $ contra $ or₁) (deductInv $ contra $ or₂)
@[simp] lemma CNAKNN! : 𝓢 ⊢! ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := ⟨CNAKNN⟩

def KNN_of_NA (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := CNAKNN ⨀ b
lemma KNN!_of_NA! (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := ⟨KNN_of_NA b.some⟩


-- TODO: Actually this can be computable but it's too slow.
noncomputable def CNKANN [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := by
  apply CN_of_CN_left;
  apply deduct';
  exact K_replace (KNN_of_NA $ FiniteContext.id) dne dne;
@[simp] lemma CNKANN! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := ⟨CNKANN⟩

noncomputable def ANN_of_NK [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := CNKANN ⨀ b
lemma ANN!_of_NK! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ := ⟨ANN_of_NK b.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def AN_of_C [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := by
  apply of_NN;
  apply N_of_CO;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := KNN_of_NA $ FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ ➝ ⊥ := CO_of_N $ K_left d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) $ contra d) ⨀ (K_right d₁);
  exact d₂ ⨀ d₃;
lemma AN!_of_C! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := ⟨AN_of_C d.some⟩

noncomputable def CCAN [HasAxiomDNE 𝓢]  : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼φ ⋎ ψ) := by
  apply deduct';
  apply AN_of_C;
  exact FiniteContext.byAxm;
lemma CCAN! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ➝ ψ) ➝ ∼φ ⋎ ψ := ⟨CCAN⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def CCNNNNNNC [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := by
  apply deduct';
  apply N_of_CO;
  exact C_trans
    (by
      apply deductInv;
      apply CC_of_CK;
      apply deduct;
      have d₁ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ➝ ∼∼ψ := K_left (ψ := ∼(φ ➝ ψ)) $ FiniteContext.id;
      have d₂ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := KNN_of_NA $ (contra CANC) ⨀ (K_right (φ := (∼∼φ ➝ ∼∼ψ)) $ FiniteContext.id)
      exact K_intro (K_right d₂) (d₁ ⨀ (K_left d₂))
    )
    (CKNO (φ := ∼ψ));

@[simp] lemma CCNNNNNNC! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := ⟨CCNNNNNNC⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def NNC_of_CNNNN [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢ ∼∼(φ ➝ ψ) := CCNNNNNNC⨀ b
lemma NNC!_of_CNNNN! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢! ∼∼(φ ➝ ψ) := ⟨NNC_of_CNNNN b.some⟩

section

instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne φ := by
    apply deduct';
    exact of_C_of_C_of_A (C_id _) (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ ➝ ⊥ := CO_of_N $ FiniteContext.byAxm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      exact of_O $ nnp ⨀ np;
    ) $ of lem;;

end


section

-- TODO: Actually this can be computable but it's too slow.
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomLEM 𝓢 where
  lem _ := A_of_ANNNN $ AN_of_C dni

instance [HasAxiomDNE 𝓢] : HasAxiomEFQ 𝓢 where
  efq φ := by
    apply C_of_CNN;
    exact C_trans (K_left negEquiv) $ C_trans (C_swap imply₁) (K_right negEquiv);

instance [HasAxiomDNE 𝓢] : HasAxiomElimContra 𝓢 where
  elimContra φ ψ := by
    apply deduct';
    have : [∼ψ ➝ ∼φ] ⊢[𝓢] ∼ψ ➝ ∼φ := FiniteContext.byAxm;
    exact C_of_CNN this;

end


noncomputable def ECAN [HasAxiomDNE 𝓢] : 𝓢 ⊢ (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := E_intro
  CCAN (deduct' (A_cases CNC imply₁ byAxm₀))

noncomputable def ECAN! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := ⟨ECAN⟩

def EConj₂Conj : (Γ : List F) → 𝓢 ⊢ ⋀Γ ⭤ Γ.conj
  | []          => E_Id ⊤
  | [_]         => E_intro (deduct' <| K_intro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => EKK_of_E_of_E (E_Id φ) (EConj₂Conj (ψ :: Γ))
omit [DecidableEq F] in @[simp] lemma EConj₂Conj! : 𝓢 ⊢! ⋀Γ ⭤ Γ.conj := ⟨EConj₂Conj Γ⟩


omit [DecidableEq F] in lemma CConj!_iff_CConj₂ : 𝓢 ⊢! Γ.conj ➝ φ ↔ 𝓢 ⊢! ⋀Γ ➝ φ := C!_iff_C!_of_iff_left $ E!_symm EConj₂Conj!

section Conjunction

/--! note: It may be easier to handle define `List.conj` based on `List.conj' (?)`  -/
def right_Conj'_intro (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ φ ➝ ψ i) : 𝓢 ⊢ φ ➝ l.conj' ψ :=
  right_Conj₂_intro φ (l.map ψ) fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (fun i ↦ ψ i = χ) (by simpa using h)
    Entailment.cast (by simp [e]) (b i hi)
lemma right_Conj'!_intro (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢! φ ➝ ψ i) : 𝓢 ⊢! φ ➝ l.conj' ψ :=
  ⟨right_Conj'_intro φ l ψ fun i hi ↦ (b i hi).get⟩

def left_Conj'_intro {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢ l.conj' φ ➝ φ i := left_Conj₂_intro (by simp; use i)
lemma left_Conj'!_intro {l : List ι} (h : i ∈ l) (φ : ι → F) : 𝓢 ⊢! l.conj' φ ➝ φ i := ⟨left_Conj'_intro h φ⟩

omit [DecidableEq F] in
lemma right_Fconj!_intro (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ s.conj :=
  right_Conj₂!_intro φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma left_Fconj!_intro {s : Finset F} (h : φ ∈ s) : 𝓢 ⊢! s.conj ➝ φ := left_Conj₂!_intro <| by simp [h]

lemma right_Fconj'!_intro (φ : F) (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢! φ ➝ ψ i) :
    𝓢 ⊢! φ ➝ ⩕ i ∈ s, ψ i := right_Conj'!_intro φ s.toList ψ (by simpa)

lemma left_Fconj'!_intro {s : Finset ι} (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢! (⩕ i ∈ s, φ i) ➝ φ i :=
  left_Conj'!_intro (by simpa) φ

lemma right_Uconj!_intro [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢! φ ➝ ψ i) :
    𝓢 ⊢! φ ➝ ⩕ i, ψ i := right_Fconj'!_intro φ Finset.univ ψ (by simpa using b)

lemma left_Uconj!_intro [Fintype ι] (φ : ι → F) (i) : 𝓢 ⊢! (⩕ i, φ i) ➝ φ i := left_Fconj'!_intro _ <| by simp

omit [DecidableEq F] in
lemma Conj₂!_iff_forall_provable {Γ : List F} : (𝓢 ⊢! ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢! φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all;
    constructor;
    . intro h;
      constructor;
      . exact K!_left h;
      . exact ih.mp (K!_right h);
    . rintro ⟨h₁, h₂⟩;
      exact K!_intro h₁ (ih.mpr h₂);

lemma CConj₂Conj₂!_of_subset (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all; exact left_Conj₂!_intro h;
  | hcons φ Γ hne ih => simp_all; exact right_K!_intro (left_Conj₂!_intro h.1) ih;

lemma CConj₂Conj₂!_of_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact C!_of_conseq! verum!;
  | hsingle => simp_all; exact provable_iff.mp h;
  | hcons φ Γ hne ih => simp_all; exact right_K!_intro (provable_iff.mp h.1) ih;

lemma CConj₂!_of_forall_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : Δ ⊢[𝓢]! ⋀Γ := provable_iff.mpr $ CConj₂Conj₂!_of_provable h

lemma CConj₂!_of_unique (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢! φ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all;
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact right_K!_intro C!_id ih;
  | _ => simp_all;

lemma C!_of_CConj₂!_of_unique (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := C!_trans (CConj₂!_of_unique he) hd

lemma CConj₂!_iff_CKConj₂! : 𝓢 ⊢! ⋀(φ :: Γ) ➝ ψ ↔ 𝓢 ⊢! φ ⋏ ⋀Γ ➝ ψ := by
  induction Γ with
  | nil =>
    simp [CK!_iff_CC!];
    constructor;
    . intro h; apply C!_swap; exact C!_of_conseq! h;
    . intro h; exact C!_swap h ⨀ verum!;
  | cons ψ ih => simp;

omit [DecidableEq F] in
@[simp] lemma CConj₂AppendKConj₂Conj₂! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct'!;
  have : [⋀(Γ ++ Δ)] ⊢[𝓢]! ⋀(Γ ++ Δ) := id!;
  have d := Conj₂!_iff_forall_provable.mp this;
  apply K!_intro;
  . apply Conj₂!_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp; left; exact hp);
  . apply Conj₂!_iff_forall_provable.mpr;
    intro φ hp;
    exact d φ (by simp; right; exact hp);

@[simp]
lemma CKConj₂RemoveConj₂! : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ➝ ⋀Γ := by
  apply deduct'!;
  apply Conj₂!_iff_forall_provable.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  . subst e; exact K!_right id!;
  . exact Conj₂!_iff_forall_provable.mp (K!_left id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma CKConj₂Remove!_of_CConj₂! (b : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ➝ ψ := C!_trans CKConj₂RemoveConj₂! b

omit [DecidableEq F] in
lemma Conj₂Append!_iff_KConj₂Conj₂! : 𝓢 ⊢! ⋀(Γ ++ Δ) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    replace h := Conj₂!_iff_forall_provable.mp h;
    apply K!_intro;
    . apply Conj₂!_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    . apply Conj₂!_iff_forall_provable.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply Conj₂!_iff_forall_provable.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    . exact (Conj₂!_iff_forall_provable.mp $ K!_left h) φ hp₁;
    . exact (Conj₂!_iff_forall_provable.mp $ K!_right h) φ hp₂;

omit [DecidableEq F] in
@[simp] lemma EConj₂AppendKConj₂Conj₂! : 𝓢 ⊢! ⋀(Γ ++ Δ) ⭤ ⋀Γ ⋏ ⋀Δ := by
  apply E!_intro;
  . apply deduct'!; apply Conj₂Append!_iff_KConj₂Conj₂!.mp; exact id!;
  . apply deduct'!; apply Conj₂Append!_iff_KConj₂Conj₂!.mpr; exact id!;

omit [DecidableEq F] in
lemma CConj₂Append!_iff_CKConj₂Conj₂! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ φ ↔ 𝓢 ⊢! (⋀Γ ⋏ ⋀Δ) ➝ φ := by
  constructor;
  . intro h; exact C!_trans (K!_right EConj₂AppendKConj₂Conj₂!) h;
  . intro h; exact C!_trans (K!_left EConj₂AppendKConj₂Conj₂!) h;

@[simp] lemma CFConjConj₂ {Γ : Finset F} : 𝓢 ⊢! ⋀Γ.toList ➝ Γ.conj := by
  apply CConj₂Conj₂!_of_provable;
  apply FiniteContext.by_axm!;

@[simp] lemma CConj₂Conj_list {Γ : List F} : 𝓢 ⊢! ⋀Γ ➝ Γ.toFinset.conj := by
  apply C!_trans ?_ CFConjConj₂;
  apply CConj₂Conj₂!_of_subset;
  simp;

@[simp] lemma CConj₂FConj {Γ : Finset F} : 𝓢 ⊢! Γ.conj ➝ ⋀Γ.toList := by
  apply right_Conj₂!_intro;
  intro φ hφ;
  apply left_Fconj!_intro;
  simpa using hφ;

@[simp] lemma CConj₂FConj_list {Γ : List F} : 𝓢 ⊢! Γ.toFinset.conj ➝ ⋀Γ := by
  apply C!_trans $ CConj₂FConj;
  apply CConj₂Conj₂!_of_subset;
  simp;

lemma FConj_DT {Γ : Finset F} : 𝓢 ⊢! Γ.conj ➝ φ ↔ Γ *⊢[𝓢]! φ := by
  constructor;
  . intro h;
    apply Context.provable_iff.mpr;
    use Γ.toList;
    constructor;
    . simp;
    . apply FiniteContext.provable_iff.mpr;
      exact C!_trans (by simp) h;
  . intro h;
    obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
    replace hΔ₂ : 𝓢 ⊢! ⋀Γ.toList ➝ φ := C!_trans (CConj₂Conj₂!_of_subset (by simpa)) $ FiniteContext.provable_iff.mp hΔ₂
    exact C!_trans (by simp) hΔ₂;

omit [DecidableEq F] in
lemma FConj!_iff_forall_provable {Γ : Finset F} : (𝓢 ⊢! Γ.conj) ↔ (∀ φ ∈ Γ, 𝓢 ⊢! φ) := by
  apply Iff.trans Conj₂!_iff_forall_provable;
  constructor <;> simp_all;

omit [DecidableEq F] in
lemma FConj_of_FConj!_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) (hΓ : 𝓢 ⊢! Γ.conj) : 𝓢 ⊢! Δ.conj := by
  rw [FConj!_iff_forall_provable] at hΓ ⊢;
  intro φ hφ;
  apply hΓ;
  apply h hφ;

omit [DecidableEq F] in
lemma CFConj_FConj!_of_subset [DecidableEq F] {Γ Δ : Finset F} (h : Δ ⊆ Γ) : 𝓢 ⊢! Γ.conj ➝ Δ.conj := by
  apply FConj_DT.mpr;
  apply FConj_of_FConj!_of_subset h;
  apply FConj_DT.mp;
  simp;

@[simp] lemma CFconjUnionKFconj! {Γ Δ : Finset F} : 𝓢 ⊢! (Γ ∪ Δ).conj ➝ Γ.conj ⋏ Δ.conj := by
  apply FConj_DT.mpr;
  apply K!_intro <;>
  . apply FConj_DT.mp;
    apply CFConj_FConj!_of_subset;
    simp;

@[simp] lemma CinsertFConjKFConj! {Γ : Finset F} : 𝓢 ⊢! (insert φ Γ).conj ➝ φ ⋏ Γ.conj := by
  suffices 𝓢 ⊢! ({φ} ∪ Γ).conj ➝ (Finset.conj {φ}) ⋏ Γ.conj by simpa using this;
  apply CFconjUnionKFconj!;

@[simp] lemma CKFconjFconjUnion! {Γ Δ : Finset F} : 𝓢 ⊢! Γ.conj ⋏ Δ.conj ➝ (Γ ∪ Δ).conj := by
  apply right_Fconj!_intro;
  simp only [Finset.mem_union];
  rintro φ (hφ | hφ);
  . apply left_K!_intro_left
    apply left_Fconj!_intro hφ;
  . apply left_K!_intro_right;
    apply left_Fconj!_intro hφ;

@[simp]
lemma CKFConjinsertFConj! {Γ : Finset F} : 𝓢 ⊢! φ ⋏ Γ.conj ➝ (insert φ Γ).conj := by
  suffices 𝓢 ⊢! (Finset.conj {φ}) ⋏ Γ.conj ➝ ({φ} ∪ Γ).conj by simpa using this;
  apply CKFconjFconjUnion!;

lemma FConj_DT' {Γ Δ : Finset F} : Γ *⊢[𝓢]! Δ.conj ➝ φ ↔ ↑(Γ ∪ Δ) *⊢[𝓢]! φ := by
  constructor;
  . intro h; exact FConj_DT.mp $ C!_trans CFconjUnionKFconj! $ CK!_iff_CC!.mpr $ FConj_DT.mpr h;
  . intro h; exact FConj_DT.mp $ CK!_iff_CC!.mp $ C!_trans CKFconjFconjUnion! $ FConj_DT.mpr h;

lemma CFconjFconj!_of_provable {Γ Δ : Finset _} (h : ∀ φ, φ ∈ Γ → Δ *⊢[𝓢]! φ) : 𝓢 ⊢! Δ.conj ➝ Γ.conj := by
  have : 𝓢 ⊢! ⋀(Δ.toList) ➝ ⋀(Γ.toList) := CConj₂Conj₂!_of_provable $ by
    intro φ hφ;
    apply Context.iff_provable_context_provable_finiteContext_toList.mp
    apply h φ;
    simpa using hφ;
  refine C!_replace ?_ ?_ this;
  . simp;
  . simp;

end Conjunction

section disjunction

def right_Disj_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ➝ Γ.disj :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (or₁ : 𝓢 ⊢ φ ➝ φ ⋎ Γ.disj)
    else
      have : φ ∈ Γ := by simpa [e] using h
      C_trans (right_Disj_intro Γ this) or₂
def right_Disj!_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ➝ Γ.disj := ⟨right_Disj_intro Γ h⟩

def left_Disj_intro [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ Γ.disj ➝ φ :=
  match Γ with
  |     [] => efq
  | ψ :: Γ => left_A_intro (b ψ (by simp)) <| left_Disj_intro Γ fun ψ h ↦ b ψ (by simp [h])
def left_Disj!_intro [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! Γ.disj ➝ φ :=
  ⟨left_Disj_intro Γ fun ψ h ↦ (b ψ h).get⟩

def right_Disj₂_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ➝ ⋁Γ :=
  match Γ with
  |     [] => by simp at h
  |    [ψ] => cast (by simp_all) (C_id φ)
  | ψ :: χ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (or₁ : 𝓢 ⊢ φ ➝ φ ⋎ ⋁(χ :: Γ))
    else
      have : φ ∈ χ :: Γ := by simpa [e] using h
      C_trans (right_Disj₂_intro _ this) or₂
def right_Disj₂!_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ➝ ⋁Γ := ⟨right_Disj₂_intro Γ h⟩

def left_Disj₂_intro [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ ⋁Γ ➝ φ :=
  match Γ with
  |     [] => efq
  |    [ψ] => b _ (by simp)
  | ψ :: χ :: Γ => left_A_intro (b ψ (by simp)) <| left_Disj₂_intro _ fun ψ h ↦ b ψ (by simp [h])
omit [DecidableEq F] in
lemma left_Disj₂!_intro [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! ⋁Γ ➝ φ :=
  ⟨left_Disj₂_intro Γ fun ψ h ↦ (b ψ h).get⟩

def right_Disj'_intro (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢ φ i ➝ l.disj' φ :=
  right_Disj₂_intro (l.map φ) (by simp; exact ⟨i, h, rfl⟩)
lemma right_Disj'!_intro (φ : ι → F) (l : List ι) (h : i ∈ l) : 𝓢 ⊢! φ i ➝ l.disj' φ := ⟨right_Disj'_intro φ l h⟩

def left_Disj'_intro [HasAxiomEFQ 𝓢] (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ ψ i ➝ φ) : 𝓢 ⊢ l.disj' ψ ➝ φ :=
  left_Disj₂_intro _ fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (ψ · = χ) (by simpa using h)
    Entailment.cast (by simp [e]) (b i hi)
lemma left_Disj'!_intro [HasAxiomEFQ 𝓢] (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢! ψ i ➝ φ) : 𝓢 ⊢! l.disj' ψ ➝ φ :=
  ⟨left_Disj'_intro l ψ fun i hi ↦ (b i hi).get⟩

lemma right_Fdisj!_intro (s : Finset F) (h : φ ∈ s) : 𝓢 ⊢! φ ➝ s.disj := right_Disj₂!_intro _ (by simp [h])

omit [DecidableEq F] in
lemma left_Fdisj!_intro [HasAxiomEFQ 𝓢] (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! s.disj ➝ φ :=
  left_Disj₂!_intro _ fun ψ h ↦ b ψ (by simpa using h)

lemma right_Fdisj'!_intro (s : Finset ι) (φ : ι → F) {i} (hi : i ∈ s) : 𝓢 ⊢! φ i ➝ ⩖ j ∈ s, φ j :=
  right_Disj'!_intro _ _ (by simp [hi])

lemma right_Udisj!_intro [Fintype ι] (φ : ι → F) : 𝓢 ⊢! φ i ➝ ⩖ j, φ j := right_Fdisj'!_intro _ _ (by simp)

lemma left_Fdisj'!_intro [HasAxiomEFQ 𝓢] (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢! ψ i ➝ φ) : 𝓢 ⊢! (⩖ i ∈ s, ψ i) ➝ φ :=
  left_Disj'!_intro _ _ (by simpa)

lemma left_Udisj!_intro [HasAxiomEFQ 𝓢] [Fintype ι] (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢! ψ i ➝ φ) : 𝓢 ⊢! (⩖ i, ψ i) ➝ φ :=
  left_Fdisj'!_intro _ _ (by simpa)

omit [DecidableEq F] in
lemma EDisj₂AppendADisj₂Disj₂! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ⭤ ⋁Γ ⋎ ⋁Δ := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! efq!;
  case hnil.hsingle =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! C!_id;
  case hsingle.hnil =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro C!_id efq!;
  case hcons.hnil =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro C!_id efq!;
  case hnil.hcons =>
    simp_all;
    apply E!_intro;
    . simp;
    . exact left_A!_intro efq! C!_id;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp ψ =>
    simp_all;
    apply E!_trans (by
      apply EAA!_of_E!_right;
      simpa using @ihp [ψ];
    ) EAAAA!;
  case hcons.hcons φ ps hps ihp ψ qs hqs ihq =>
    simp_all;
    exact E!_trans (by
      apply EAA!_of_E!_right;
      exact E!_trans (@ihp (ψ :: qs)) (by
        apply EAA!_of_E!_right;
        simp_all;
      )
    ) EAAAA!;

omit [DecidableEq F] in
lemma Disj₂Append!_iff_ADisj₂Disj₂! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ↔ 𝓢 ⊢! ⋁Γ ⋎ ⋁Δ := by
  constructor;
  . intro h; exact (K!_left EDisj₂AppendADisj₂Disj₂!) ⨀ h;
  . intro h; exact (K!_right EDisj₂AppendADisj₂Disj₂!) ⨀ h;

omit [DecidableEq F] in
lemma CDisj₂!_iff_CADisj₂! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ⋁(ψ :: Γ) ↔ 𝓢 ⊢! φ ➝ ψ ⋎ ⋁Γ := by
  induction Γ with
  | nil =>
    simp;
    constructor;
    . intro h; exact C!_trans h or₁!;
    . intro h; exact C!_trans h $ left_A!_intro C!_id efq!;
  | cons ψ ih => simp;

@[simp]
lemma CDisj₂ADisj₂Remove! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁Γ ➝ φ ⋎ ⋁(Γ.remove φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp;
    by_cases h: ψ = φ;
    . subst_vars; simp;
    . simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all;
    by_cases hpq : ψ = φ;
    . simp_all only [ne_eq, List.remove_cons_self]; exact left_A!_intro or₁! ih;
    . simp_all [(List.remove_cons_of_ne Γ hpq)];
      by_cases hqΓ : Γ.remove φ = [];
      . simp_all;
        exact left_A!_intro or₂! (C!_trans ih $ CAA!_of_C!_right efq!);
      . simp_all;
        exact left_A!_intro (C!_trans or₁! or₂!) (C!_trans ih (CAA!_of_C!_right or₂!));

lemma left_Disj₂!_intro' [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢! ⋁Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ ih =>
    simp_all;
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact of_C!_of_C!_of_A! (by simp) (weakening! (by simp) $ provable_iff_provable.mp $ ih) id!
  | _ => simp_all;

lemma of_Disj₂!_of_mem_eq [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : 𝓢 ⊢! ⋁Γ) : 𝓢 ⊢! φ := (left_Disj₂!_intro' hd) ⨀ h


@[simp] lemma CFDisjDisj₂ [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! ⋁Γ.toList ➝ Γ.disj := by
  apply left_Disj₂!_intro;
  intro ψ hψ;
  apply right_Fdisj!_intro;
  simpa using hψ;

@[simp] lemma CDisj₂Disj [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! Γ.disj ➝ ⋁Γ.toList := by
  apply left_Fdisj!_intro;
  intro ψ hψ;
  apply right_Disj₂!_intro;
  simpa;

lemma CDisj₂Disj₂_of_subset [HasAxiomEFQ 𝓢] {Γ Δ : List F} (h : ∀ φ ∈ Γ, φ ∈ Δ) : 𝓢 ⊢! ⋁Γ ➝ ⋁Δ := by
  match Δ with
  | [] =>
    have : Γ = [] := List.iff_nil_forall.mpr h;
    subst this;
    simp;
  | [φ] =>
    apply left_Disj₂!_intro;
    intro ψ hψ;
    have := h ψ hψ;
    simp_all;
  | φ :: Δ =>
    apply left_Disj₂!_intro;
    intro ψ hψ;
    apply right_Disj₂!_intro;
    apply h;
    exact hψ;

lemma CFDisjFDisj_of_subset [HasAxiomEFQ 𝓢] {Γ Δ : Finset F} (h : Γ ⊆ Δ) : 𝓢 ⊢! Γ.disj ➝ Δ.disj := by
  refine C!_trans (C!_trans ?_ (CDisj₂Disj₂_of_subset (Γ := Γ.toList) (Δ := Δ.toList) (by simpa))) ?_ <;> simp;

lemma EDisj₂FDisj {Γ : List F} [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁Γ ⭤ Γ.toFinset.disj := by
  match Γ with
  | [] => simp;
  | φ :: Γ =>
    apply E!_intro;
    . apply left_Disj₂!_intro;
      simp only [List.mem_cons, List.toFinset_cons, forall_eq_or_imp];
      constructor;
      . apply right_Fdisj!_intro;
        simp_all;
      . intro ψ hψ;
        apply right_Fdisj!_intro;
        simp_all;
    . apply left_Fdisj!_intro;
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, forall_eq_or_imp];
      constructor;
      . apply right_Disj₂!_intro;
        tauto;
      . intro ψ hψ;
        apply right_Disj₂!_intro;
        tauto;

lemma EDisj₂FDisj!_doubleton [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁[φ, ψ] ⭤ Finset.disj {φ, ψ} := by
  convert EDisj₂FDisj (𝓢 := 𝓢) (Γ := [φ, ψ]);
  simp;

lemma EConj₂_FConj!_doubleton [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁[φ, ψ] ↔ 𝓢 ⊢! Finset.disj {φ, ψ} := by
  constructor;
  . intro h; exact (C_of_E_mp! $ EDisj₂FDisj!_doubleton) ⨀ h;
  . intro h; exact (C_of_E_mpr! $ EDisj₂FDisj!_doubleton) ⨀ h;

@[simp]
lemma CAFDisjinsertFDisj! [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! φ ⋎ Γ.disj ➝ (insert φ Γ).disj := by
  apply left_A!_intro;
  . apply right_Fdisj!_intro; simp;
  . apply CFDisjFDisj_of_subset; simp;

@[simp]
lemma CinsertFDisjAFDisj! [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! (insert φ Γ).disj ➝ φ ⋎ Γ.disj := by
  apply left_Fdisj!_intro;
  simp only [Finset.mem_insert, forall_eq_or_imp, or₁!, true_and];
  intro ψ hψ;
  apply right_A!_intro_right;
  apply right_Fdisj!_intro;
  assumption;

@[simp] lemma CAFdisjFdisjUnion [HasAxiomEFQ 𝓢] {Γ Δ : Finset F} : 𝓢 ⊢! Γ.disj ⋎ Δ.disj ➝ (Γ ∪ Δ).disj := by
  apply left_A!_intro <;>
  . apply CFDisjFDisj_of_subset;
    simp;

@[simp]
lemma CFdisjUnionAFdisj [HasAxiomEFQ 𝓢] {Γ Δ : Finset F} : 𝓢 ⊢! (Γ ∪ Δ).disj ➝ Γ.disj ⋎ Δ.disj := by
  apply left_Fdisj!_intro;
  simp only [Finset.mem_union];
  rintro ψ (hψ | hψ);
  . apply C!_trans (ψ := Γ.disj) ?_ or₁!;
    apply right_Fdisj!_intro;
    assumption;
  . apply C!_trans (ψ := Δ.disj) ?_ or₂!;
    apply right_Fdisj!_intro;
    assumption;

lemma left_Fdisj!_intro' {Γ : Finset _} [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢! Γ.disj ➝ φ := by
  apply C!_trans ?_ $ left_Disj₂!_intro' (Γ := Γ.toList) (by simpa);
  simp;

end disjunction


section

variable {Γ Δ : Finset F}

lemma CFConj_CDisj!_of_A [HasAxiomEFQ 𝓢] (hφψ : φ ⋎ ψ ∈ Γ) (hφ : φ ∈ Δ) (hψ : ψ ∈ Δ) : 𝓢 ⊢! Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {φ, ψ});
  . apply C!_trans (ψ := Finset.conj {φ ⋎ ψ}) ?_;
    . apply FConj_DT.mpr;
      suffices ↑{φ ⋎ ψ} *⊢[𝓢]! [φ, ψ].disj₂ by simpa using EConj₂_FConj!_doubleton.mp this;
      apply Context.by_axm!;
      simp;
    . apply CFConj_FConj!_of_subset;
      simpa;
  . apply left_Fdisj!_intro;
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq];
    constructor <;>
    . apply right_Fdisj!_intro;
      assumption;

lemma CFConj_CDisj!_of_K_intro (hp : φ ∈ Γ) (hpq : ψ ∈ Γ) (hψ : φ ⋏ ψ ∈ Δ) : 𝓢 ⊢! Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {φ ⋏ ψ});
  . apply C!_trans (ψ := Finset.conj {φ, ψ}) ?_;
    . apply FConj_DT.mpr;
      simp only [Finset.coe_insert, Finset.coe_singleton, Finset.disj_singleton];
      apply K!_intro <;> exact Context.by_axm! $ by simp;
    . apply CFConj_FConj!_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj!_intro _ hψ;

lemma CFConj_CDisj!_of_innerMDP (hp : φ ∈ Γ) (hpq : φ ➝ ψ ∈ Γ) (hψ : ψ ∈ Δ) : 𝓢 ⊢! Γ.conj ➝ Δ.disj := by
  apply C!_trans (ψ := Finset.disj {ψ});
  . apply C!_trans (ψ := Finset.conj {φ, φ ➝ ψ}) ?_;
    . apply FConj_DT.mpr;
      have h₁ : ({φ, φ ➝ ψ}) *⊢[𝓢]! φ ➝ ψ := Context.by_axm! $ by simp;
      have h₂ : ({φ, φ ➝ ψ}) *⊢[𝓢]! φ := Context.by_axm! $ by simp;
      simpa using h₁ ⨀ h₂;
    . apply CFConj_FConj!_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  . simp only [Finset.disj_singleton];
    apply right_Fdisj!_intro _ hψ;

lemma iff_FiniteContext_Context {Γ : List F} : Γ ⊢[𝓢]! φ ↔ ↑Γ.toFinset *⊢[𝓢]! φ := by
  constructor;
  . intro h;
    replace h := FiniteContext.provable_iff.mp h;
    apply FConj_DT.mp;
    exact C!_trans (by simp) h;
  . intro h;
    replace h := FConj_DT.mpr h;
    apply FiniteContext.provable_iff.mpr;
    exact C!_trans (by simp) h;

end


section

/-- List version of `CNAKNN!` -/
@[simp]
lemma CNDisj₁Conj₂! : 𝓢 ⊢! ∼⋁Γ ➝ ⋀(Γ.map (∼·)) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    refine C!_trans CNAKNN! ?_;
    apply CKK!_of_C!' ih;

/--- Finset version of `CNAKNN!` -/
@[simp]
lemma CNFdisjFconj! [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! ∼Γ.disj ➝ (Γ.image (∼·)).conj := by
  apply C!_replace ?_ ?_ $ CNDisj₁Conj₂! (Γ := Γ.toList);
  . apply contra!;
    exact CFDisjDisj₂;
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CConj₂NNDisj₂! : 𝓢 ⊢! ⋀Γ.map (∼·) ➝ ∼⋁Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    apply C!_trans ?_ CKNNNA!;
    apply CKK!_of_C!' ih;

/--- Finset version of `CKNNNA!` -/
@[simp]
lemma CFconjNNFconj! [HasAxiomEFQ 𝓢] {Γ : Finset F} : 𝓢 ⊢! (Γ.image (∼·)).conj ➝ ∼Γ.disj := by
  apply C!_replace ?_ ?_ $ CConj₂NNDisj₂! (Γ := Γ.toList);
  . apply CConj₂Conj₂!_of_provable;
    intro φ hφ;
    apply FiniteContext.by_axm!
    simpa using hφ;
  . apply contra!;
    simp;

@[simp]
lemma CNDisj₂NConj₂! [HasAxiomDNE 𝓢] {Γ : List F} : 𝓢 ⊢! ∼⋁(Γ.map (∼·)) ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢! ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) ➝ φ ⋏ ⋀Γ by
      apply C!_trans ?_ this;
      apply contra!;
      apply CAA!_of_C!_right;
      exact dne!;
    apply C!_trans CNAKNN! ?_;
    apply CKK!_of_C!_of_C!;
    . exact dne!;
    . exact C!_trans dne! ih;

lemma CNFdisj₂NFconj₂! [HasAxiomDNE 𝓢] {Γ : Finset F} : 𝓢 ⊢! ∼(Γ.image (∼·)).disj ➝ Γ.conj := by
  apply C!_replace ?_ ?_ $ CNDisj₂NConj₂! (Γ := Γ.toList);
  . apply contra!;
    apply left_Disj₂!_intro;
    intro ψ hψ;
    apply right_Fdisj!_intro;
    simpa using hψ;
  . simp;

end


namespace Context

lemma provable_iff_finset {Γ : Set F} {φ : F} : Γ *⊢[𝓢]! φ ↔ ∃ Δ : Finset F, (Δ.toSet ⊆ Γ) ∧ Δ *⊢[𝓢]! φ := by
  apply Iff.trans Context.provable_iff;
  constructor;
  . rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toFinset;
    constructor;
    . simpa;
    . apply provable_iff.mpr
      use Δ;
      constructor <;> simp_all;
  . rintro ⟨Δ, hΔ₁, hΔ₂⟩;
    use Δ.toList;
    constructor;
    . simpa;
    . apply FiniteContext.provable_iff.mpr;
      refine C!_trans ?_ (FConj_DT.mpr hΔ₂);
      simp;

lemma bot_of_mem_neg  {Γ : Set F}  (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ *⊢[𝓢]! ⊥ := by
  replace h₁ : Γ *⊢[𝓢]! φ := by_axm! h₁;
  replace h₂ : Γ *⊢[𝓢]! φ ➝ ⊥ := N!_iff_CO!.mp $ by_axm! h₂;
  exact h₂ ⨀ h₁;

end Context



section classical

variable [Entailment.Cl 𝓢]

lemma not_imply_prem''! (hpq : 𝓢 ⊢! φ ➝ ψ) (hpnr : 𝓢 ⊢! φ ➝ ∼ξ) : 𝓢 ⊢! φ ➝ ∼(ψ ➝ ξ) :=
  deduct'! $ (contra! $ CCAN!) ⨀ (NA!_of_KNN! $ K!_intro (dni'! $ of'! hpq ⨀ (by_axm!)) (of'! hpnr ⨀ (by_axm!)))

def ofAOfN (b : 𝓢 ⊢ φ ⋎ ψ) (d : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := A_cases (C_of_CNN (dhyp d)) (C_id _) b

def of_a!_of_n! (b : 𝓢 ⊢! φ ⋎ ψ) (d : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! ψ := ⟨ofAOfN b.get d.get⟩

end classical

section consistency

variable [HasAxiomEFQ 𝓢]

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢! φ) (hn : 𝓢 ⊢! ∼φ) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢! φ ➝ ⊥ := N!_iff_CO!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end consistency

end LO.Entailment

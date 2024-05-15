import Logic.Logic.HilbertStyle.Supplemental
import Logic.Modal.Standard.System

namespace LO.System

variable {F : Type*} [StandardModalLogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F} {Γ Δ : List F}

variable {𝓢 : S}
variable [Classical 𝓢]


open FiniteContext

open Necessitation

variable [Necessitation 𝓢]

lemma Necessitation.nec! : 𝓢 ⊢! p → 𝓢 ⊢! □p := by
  rintro ⟨hp⟩;
  exact ⟨nec hp⟩

def Necessitation.multinec : 𝓢 ⊢ p → 𝓢 ⊢ □^[n]p := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;

lemma Necessitation.multinec! : 𝓢 ⊢! p → 𝓢 ⊢! □^[n]p := by
  rintro ⟨hp⟩;
  exact ⟨multinec hp⟩

variable [HasAxiomK 𝓢]

def axiomK : 𝓢 ⊢ □(p ⟶ q) ⟶ □p ⟶ □q := HasAxiomK.K _ _
@[simp] lemma axiomK! : 𝓢 ⊢! □(p ⟶ q) ⟶ □p ⟶ □q := ⟨axiomK⟩

instance [HasAxiomK 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ of axiomK⟩

def axiomK' (h : 𝓢 ⊢ □(p ⟶ q)) : 𝓢 ⊢ □p ⟶ □q := axiomK ⨀ h
@[simp] lemma axiomK'! (h : 𝓢 ⊢! □(p ⟶ q)) : 𝓢 ⊢! □p ⟶ □q := ⟨axiomK' h.some⟩

alias boxedImplyDistribute := axiomK'
alias boxed_imply_distribute! := axiomK'!

def axiomK'' (h₁ : 𝓢 ⊢ □(p ⟶ q)) (h₂ : 𝓢 ⊢ □p) : 𝓢 ⊢ □q := axiomK' h₁ ⨀ h₂
@[simp] lemma axiomK''! (h₁ : 𝓢 ⊢! □(p ⟶ q)) (h₂ : 𝓢 ⊢! □p) : 𝓢 ⊢! □q := ⟨axiomK'' h₁.some h₂.some⟩

def multibox_axiomK : 𝓢 ⊢ □^[n](p ⟶ q) ⟶ □^[n]p ⟶ □^[n]q := by
  induction n with
  | zero => simp; apply impId;
  | succ n ih => simpa using impTrans (boxedImplyDistribute $ nec ih) (by apply axiomK);

@[simp] lemma multibox_axiomK! : 𝓢 ⊢! □^[n](p ⟶ q) ⟶ □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK⟩

def multibox_axiomK' (h : 𝓢 ⊢ □^[n](p ⟶ q)) : 𝓢 ⊢ □^[n]p ⟶ □^[n]q := multibox_axiomK ⨀ h
@[simp] lemma multibox_axiomK'! (h : 𝓢 ⊢! □^[n](p ⟶ q)) : 𝓢 ⊢! □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK' h.some⟩

alias multiboxedImplyDistribute := multibox_axiomK'
alias multiboxed_imply_distribute! := multibox_axiomK'!

/-
def multiboxedIffDistribute : 𝓢 ⊢ □^[n](p ⟷ q) ⟶ □^[n]p ⟷ □^[n]q := by
  simp [LogicalConnective.iff];
-/
def boxIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (□p ⟷ □q) := by sorry;
@[simp] lemma box_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □p ⟷ □q := ⟨boxIff' h.some⟩

def multibox_iff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ □^[n]p ⟷ □^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
@[simp] lemma multibox_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □^[n]p ⟷ □^[n]q := ⟨multibox_iff' h.some⟩

def negIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (~p ⟷ ~q) := conj₃' (contra₀' $ conj₂' h) (contra₀' $ conj₁' h)
@[simp] lemma neg_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ~p ⟷ ~q := ⟨negIff' h.some⟩

def diaIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (◇p ⟷ ◇q) := by
  simp only [StandardModalLogicalConnective.duality'];
  apply negIff';
  apply boxIff';
  apply negIff';
  assumption
@[simp] lemma dia_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ◇p ⟷ ◇q := ⟨diaIff' h.some⟩

def multidiaIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ ◇^[n]p ⟷ ◇^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
@[simp] lemma multidia_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ◇^[n]p ⟷ ◇^[n]q := ⟨multidiaIff' h.some⟩

def conjL (hq : 𝓢 ⊢ p ⟶ q) (hr : 𝓢 ⊢ p ⟶ r) : 𝓢 ⊢ p ⟶ q ⋏ r := by
  apply emptyPrf;
  apply deduct;
  replace hq : [] ⊢[𝓢] p ⟶ q := of hq;
  replace hr : [] ⊢[𝓢] p ⟶ r := of hr;
  exact conj₃' (mdp' hq (FiniteContext.byAxm (by simp))) (mdp' hr (FiniteContext.byAxm (by simp)))
@[simp] lemma conjL! (hq : 𝓢 ⊢! p ⟶ q) (hr : 𝓢 ⊢! p ⟶ r) : 𝓢 ⊢! p ⟶ q ⋏ r := ⟨conjL hq.some hr.some⟩

def implyBoxDistribute (h : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ □p ⟶ □q := axiomK' $ nec h
@[simp] lemma imply_box_distribute! (h : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! □p ⟶ □q := ⟨implyBoxDistribute h.some⟩

def distribute_box_conj : 𝓢 ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := conjL (implyBoxDistribute conj₁) (implyBoxDistribute conj₂)
@[simp] lemma distribute_box_conj! : 𝓢 ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_conj⟩

def distribute_box_conj' (h : 𝓢 ⊢ □(p ⋏ q)) : 𝓢 ⊢ □p ⋏ □q := distribute_box_conj ⨀ h
@[simp] lemma distribute_box_conj'! (d : 𝓢 ⊢! □(p ⋏ q)) : 𝓢 ⊢! □p ⋏ □q := ⟨distribute_box_conj' d.some⟩

def collect_box_conj : 𝓢 ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := by
  have d₁ : 𝓢 ⊢ □p ⟶ □(q ⟶ p ⋏ q) := implyBoxDistribute conj₃;
  have d₂ : 𝓢 ⊢ □(q ⟶ p ⋏ q) ⟶ (□q ⟶ □(p ⋏ q)) := axiomK;
  exact (conj₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans d₁ d₂);
@[simp] lemma collect_box_conj! : 𝓢 ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_conj⟩


def collect_box_or : 𝓢 ⊢ □p ⋎ □q ⟶ □(p ⋎ q) := disj₃'' (axiomK' $ nec disj₁) (axiomK' $ nec disj₂)
@[simp] lemma collect_box_or! : 𝓢 ⊢! □p ⋎ □q ⟶ □(p ⋎ q) := ⟨collect_box_or⟩

variable [HasAxiomFour 𝓢]

def axiomFour : 𝓢 ⊢ □p ⟶ □□p := HasAxiomFour.Four _
@[simp] lemma axiomFour! : 𝓢 ⊢! □p ⟶ □□p := ⟨axiomFour⟩

instance [HasAxiomFour 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ of axiomFour⟩


variable [HasAxiomT 𝓢]

def axiomT : 𝓢 ⊢ □p ⟶ p := HasAxiomT.T _
@[simp] lemma axiomT! : 𝓢 ⊢! □p ⟶ p := ⟨axiomT⟩

instance [HasAxiomT 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ of axiomT⟩

def axiomT' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ p := axiomT ⨀ h
@[simp] lemma axiomT'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! p := ⟨axiomT' h.some⟩

end LO.System

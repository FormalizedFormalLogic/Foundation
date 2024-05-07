import Logic.Logic.System
import Logic.Logic.HilbertStyle.Context

namespace LO.System

variable {F : Type*} [LogicalConnective F] [NegDefinition F] [DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F}

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

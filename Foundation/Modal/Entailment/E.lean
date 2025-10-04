import Foundation.Modal.Entailment.DiaDuality

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} [Entailment.E 𝓢] {n : ℕ} {φ ψ ξ χ: F}

variable [DecidableEq F]

def ELLNN! : 𝓢 ⊢! □φ ⭤ □(∼∼φ) := by apply re; exact dn;
@[simp] lemma ELLNN : 𝓢 ⊢ □φ ⭤ □(∼∼φ) := ⟨ELLNN!⟩

def ILLNN! : 𝓢 ⊢! □φ ➝ □(∼∼φ) := K_left ELLNN!
@[simp] lemma ILLNN : 𝓢 ⊢ □φ ➝ □(∼∼φ) := ⟨ILLNN!⟩
alias box_dni := ILLNN!
alias box_dni! := ILLNN

def ILNNL! : 𝓢 ⊢! □(∼∼φ) ➝ □φ := K_right ELLNN!
@[simp] lemma ILNNL : 𝓢 ⊢ □(∼∼φ) ➝ □φ := ⟨ILNNL!⟩
alias box_dne := ILNNL!
alias box_dne! := ILNNL

def box_dne' (h : 𝓢 ⊢! □(∼∼φ)): 𝓢 ⊢! □φ := box_dne ⨀ h
@[grind →] lemma box_dne'! (h : 𝓢 ⊢ □(∼∼φ)): 𝓢 ⊢ □φ := ⟨box_dne' h.some⟩

@[simp] lemma INMNL : 𝓢 ⊢ ∼◇(∼φ) ➝ □φ := by
  apply CN!_of_CN!_left;
  apply C!_trans ?_ INLNM;
  apply contra!;
  simp;

@[simp] lemma INLMN :  𝓢 ⊢ ∼□φ ➝ ◇(∼φ) := by
  apply CN!_of_CN!_left;
  simp;

end LO.Modal.Entailment

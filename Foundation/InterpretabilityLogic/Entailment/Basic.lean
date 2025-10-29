import Foundation.InterpretabilityLogic.Axioms
import Foundation.Modal.Entailment.Basic

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomJ1 (𝓢 : S) where
  J1! {φ ψ : F} : 𝓢 ⊢! Axioms.J1 φ ψ
export HasAxiomJ1 (J1!)

section

variable [HasAxiomJ1 𝓢]

@[simp] lemma J1 : 𝓢 ⊢ Axioms.J1 φ ψ := ⟨J1!⟩

variable [ModusPonens 𝓢]

def rhdOfLC! (h : 𝓢 ⊢! □(φ ➝ ψ)) : 𝓢 ⊢! (φ ▷ ψ) := J1! ⨀ h

@[grind]
lemma rhd_of_lc (h : 𝓢 ⊢ □(φ ➝ ψ)) : 𝓢 ⊢ (φ ▷ ψ) := ⟨rhdOfLC! h.some⟩

end


class HasAxiomJ2 (𝓢 : S) where
  J2! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2 φ ψ χ
export HasAxiomJ2 (J2!)


section

variable [HasAxiomJ2 𝓢]

@[simp] lemma J2 : 𝓢 ⊢ Axioms.J2 φ ψ χ := ⟨J2!⟩

variable [ModusPonens 𝓢]

def rhdTrans! (h₁ : 𝓢 ⊢! φ ▷ ψ) (h₂ : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ▷ χ) := J2! ⨀ h₁ ⨀ h₂

@[grind]
lemma rhd_trans (h₁ : 𝓢 ⊢ φ ▷ ψ) (h₂ : 𝓢 ⊢ ψ ▷ χ) : 𝓢 ⊢ (φ ▷ χ) := ⟨rhdTrans! h₁.some h₂.some⟩

end


class HasAxiomJ3 (𝓢 : S) where
  J3! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J3 φ ψ χ
export HasAxiomJ3 (J3!)


section

variable [HasAxiomJ3 𝓢]

@[simp] lemma J3 : 𝓢 ⊢ Axioms.J3 φ ψ χ := ⟨J3!⟩

variable [ModusPonens 𝓢]

def rhdDilemma! (h₁ : 𝓢 ⊢! φ ▷ χ) (h₂ : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ⋎ ψ) ▷ χ := J3! ⨀ h₁ ⨀ h₂

@[grind]
lemma rhd_dilemma (h₁ : 𝓢 ⊢ φ ▷ χ) (h₂ : 𝓢 ⊢ ψ ▷ χ) : 𝓢 ⊢ (φ ⋎ ψ) ▷ χ := ⟨rhdDilemma! h₁.some h₂.some⟩

end



class HasAxiomJ4 (𝓢 : S) where
  J4! {φ ψ : F} : 𝓢 ⊢! Axioms.J4 φ ψ
export HasAxiomJ4 (J4!)


section

variable [HasAxiomJ4 𝓢]

@[simp] lemma J4 : 𝓢 ⊢ Axioms.J4 φ ψ := ⟨J4!⟩

variable [ModusPonens 𝓢]

def CMM_of_Rhd! (h : 𝓢 ⊢! φ ▷ ψ) : 𝓢 ⊢! (◇φ ➝ ◇ψ) := J4! ⨀ h
@[grind] lemma CMM_of_rhd (h : 𝓢 ⊢ φ ▷ ψ) : 𝓢 ⊢ (◇φ ➝ ◇ψ) := ⟨CMM_of_Rhd! h.some⟩

end


class HasAxiomJ5 (𝓢 : S) where
  J5! {φ : F} : 𝓢 ⊢! Axioms.J5 φ
export HasAxiomJ5 (J5!)

@[simp] lemma J5 [HasAxiomJ5 𝓢] : 𝓢 ⊢ Axioms.J5 φ := ⟨J5!⟩


class HasAxiomPP (𝓢 : S) where
  PP! {φ ψ : F} : 𝓢 ⊢! Axioms.PP φ ψ
export HasAxiomPP (PP!)

class HasAxiomMP (𝓢 : S) where
  MP! {φ ψ χ : F} : 𝓢 ⊢! Axioms.MP φ ψ χ
export HasAxiomMP (MP!)

end LO.InterpretabilityLogic.Entailment

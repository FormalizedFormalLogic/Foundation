import Foundation.InterpretabilityLogic.Axioms
import Foundation.Modal.Entailment.Basic

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasRule1 (𝓢 : S) where
  R1! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! χ ▷ φ ➝ χ ▷ ψ
export HasRule1 (R1!)

section

variable [HasRule1 𝓢]
@[grind] lemma R1 (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ χ ▷ φ ➝ χ ▷ ψ := ⟨R1! h.some⟩

variable [Entailment.Cl 𝓢]

def R1E! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! χ ▷ φ ⭤ χ ▷ ψ := K_intro (R1! $ K_left h) (R1! $ K_right h)
@[grind] lemma R1E (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ χ ▷ φ ⭤ χ ▷ ψ := ⟨R1E! h.some⟩

end


class HasRule2 (𝓢 : S) where
  R2! {φ ψ χ : F} : 𝓢 ⊢! φ ➝ ψ → 𝓢 ⊢! ψ ▷ χ ➝ φ ▷ χ
export HasRule2 (R2!)

section

variable [HasRule2 𝓢]

@[grind] lemma R2 (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ψ ▷ χ ➝ φ ▷ χ := ⟨R2! h.some⟩

variable [Entailment.Cl 𝓢]

def R2E! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ▷ χ ⭤ φ ▷ χ := K_intro (R2! $ K_left h) (R2! $ K_right h)
@[grind] lemma R2E (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ▷ χ ⭤ φ ▷ χ := ⟨R2E! h.some⟩

end



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

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ1 Γ := ⟨λ {_} => of J1!⟩

open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ1 Γ := ⟨λ {_} => of J1!⟩

end


class HasAxiomJ1' (𝓢 : S) where
  J1'! {φ : F} : 𝓢 ⊢! Axioms.J1' φ
export HasAxiomJ1' (J1'!)

section

variable [HasAxiomJ1' 𝓢]

@[simp] lemma J1' {φ : F} : 𝓢 ⊢ Axioms.J1' φ := ⟨J1'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ1' Γ := ⟨λ {_} => of J1'!⟩

open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ1' Γ := ⟨λ {_} => of J1'!⟩

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

class HasAxiomJ2Plus (𝓢 : S) where
  J2Plus! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2Plus φ ψ χ
export HasAxiomJ2Plus (J2Plus!)

section

variable [HasAxiomJ2Plus 𝓢]
@[simp] lemma J2Plus : 𝓢 ⊢ Axioms.J2Plus φ ψ χ := ⟨J2Plus!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ2Plus Γ := ⟨λ {_} => of J2Plus!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ2Plus Γ := ⟨λ {_} => of J2Plus!⟩

end


class HasAxiomJ2Plus' (𝓢 : S) where
  J2Plus'! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2Plus' φ ψ χ
export HasAxiomJ2Plus' (J2Plus'!)

section

variable [HasAxiomJ2Plus' 𝓢]
@[simp] lemma J2Plus' : 𝓢 ⊢ Axioms.J2Plus' φ ψ χ := ⟨J2Plus'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ2Plus' Γ := ⟨λ {_} => of J2Plus'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ2Plus' Γ := ⟨λ {_} => of J2Plus'!⟩

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

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4 Γ := ⟨λ {_} => of J4!⟩

open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4 Γ := ⟨λ {_} => of J4!⟩

variable [ModusPonens 𝓢]

def CMM_of_Rhd! (h : 𝓢 ⊢! φ ▷ ψ) : 𝓢 ⊢! (◇φ ➝ ◇ψ) := J4! ⨀ h
@[grind] lemma CMM_of_rhd (h : 𝓢 ⊢ φ ▷ ψ) : 𝓢 ⊢ (◇φ ➝ ◇ψ) := ⟨CMM_of_Rhd! h.some⟩

end


class HasAxiomJ4' (𝓢 : S) where
  J4'! {φ ψ : F} : 𝓢 ⊢! Axioms.J4' φ ψ
export HasAxiomJ4' (J4'!)

section

variable [HasAxiomJ4' 𝓢]

@[simp] lemma J4' {φ ψ : F} : 𝓢 ⊢ Axioms.J4' φ ψ := ⟨J4'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4' Γ := ⟨λ {_} => of J4'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4' Γ := ⟨λ {_} => of J4'!⟩

end


class HasAxiomJ4Plus (𝓢 : S) where
  J4Plus! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus φ ψ χ
export HasAxiomJ4Plus (J4Plus!)

section

variable [HasAxiomJ4Plus 𝓢]
@[simp] lemma J4Plus : 𝓢 ⊢ Axioms.J4Plus φ ψ χ := ⟨J4Plus!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus Γ := ⟨λ {_} => of J4Plus!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus Γ := ⟨λ {_} => of J4Plus!⟩

end


class HasAxiomJ4Plus' (𝓢 : S) where
  J4Plus'! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus' φ ψ χ
export HasAxiomJ4Plus' (J4Plus'!)

section

variable [HasAxiomJ4Plus' 𝓢]
@[simp] lemma J4Plus' : 𝓢 ⊢ Axioms.J4Plus' φ ψ χ := ⟨J4Plus'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus' Γ := ⟨λ {_} => of J4Plus'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus' Γ := ⟨λ {_} => of J4Plus'!⟩

end


class HasAxiomJ4Plus'' (𝓢 : S) where
  J4Plus''! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus'' φ ψ χ
export HasAxiomJ4Plus'' (J4Plus''!)

section

variable [HasAxiomJ4Plus'' 𝓢]
@[simp] lemma J4Plus'' : 𝓢 ⊢ Axioms.J4Plus'' φ ψ χ := ⟨J4Plus''!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus'' Γ := ⟨λ {_} => of J4Plus''!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus'' Γ := ⟨λ {_} => of J4Plus''!⟩

end


class HasAxiomJ5 (𝓢 : S) where
  J5! {φ : F} : 𝓢 ⊢! Axioms.J5 φ
export HasAxiomJ5 (J5!)

@[simp] lemma J5 [HasAxiomJ5 𝓢] : 𝓢 ⊢ Axioms.J5 φ := ⟨J5!⟩


class HasAxiomJ6 (𝓢 : S) where
  J6! {φ : F} : 𝓢 ⊢! Axioms.J6 φ
export HasAxiomJ6 (J6!)

section

variable [HasAxiomJ6 𝓢]

@[simp] lemma J6 : 𝓢 ⊢ Axioms.J6 φ := ⟨J6!⟩

variable [Entailment.Cl 𝓢]

def CLRhdNO! : 𝓢 ⊢! □φ ➝ (∼φ ▷ ⊥) := K_left $ J6!
@[simp, grind] lemma CLRhdNO : 𝓢 ⊢ □φ ➝ (∼φ ▷ ⊥) := ⟨CLRhdNO!⟩

def CRhdNOL! : 𝓢 ⊢! (∼φ ▷ ⊥) ➝ □φ := K_right $ J6!
@[simp, grind] lemma CRhdNOL : 𝓢 ⊢ (∼φ ▷ ⊥) ➝ □φ := ⟨CRhdNOL!⟩

def NrhdO!_of_L! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! (∼φ ▷ ⊥) := CLRhdNO! ⨀ h
@[grind] lemma NrhdO_of_L (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ (∼φ ▷ ⊥) := ⟨NrhdO!_of_L! h.some⟩

def L!_of_NrhdO! (h : 𝓢 ⊢! ∼φ ▷ ⊥) : 𝓢 ⊢! □φ := CRhdNOL! ⨀ h
@[grind] lemma L_of_NrhdO (h : 𝓢 ⊢ ∼φ ▷ ⊥) : 𝓢 ⊢ □φ := ⟨L!_of_NrhdO! h.some⟩

end


class HasAxiomP (𝓢 : S) where
  PP! {φ ψ : F} : 𝓢 ⊢! Axioms.P φ ψ
export HasAxiomP (PP!)


class HasAxiomM (𝓢 : S) where
  M! {φ ψ χ : F} : 𝓢 ⊢! Axioms.M φ ψ χ
export HasAxiomM (M!)

section

variable [HasAxiomM 𝓢]
@[simp] lemma M : 𝓢 ⊢ Axioms.M φ ψ χ := ⟨M!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomM Γ := ⟨λ {_} => of M!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomM Γ := ⟨λ {_} => of M!⟩

end


class HasAxiomKM1 (𝓢 : S) where
  KM1! {φ ψ : F} : 𝓢 ⊢! Axioms.KM1 φ ψ
export HasAxiomKM1 (KM1!)

section
variable [HasAxiomKM1 𝓢]
@[simp] lemma KM1 : 𝓢 ⊢ Axioms.KM1 φ ψ := ⟨KM1!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKM1 Γ := ⟨λ {_} => of KM1!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomKM1 Γ := ⟨λ {_} => of KM1!⟩
end

end LO.InterpretabilityLogic.Entailment

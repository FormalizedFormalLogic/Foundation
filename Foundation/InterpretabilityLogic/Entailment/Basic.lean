module

public import Foundation.InterpretabilityLogic.Axioms
public import Foundation.Modal.Entailment.Basic

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasRule1 (𝓢 : S) where
  R1! {φ ψ χ : F} : 𝓢 ⊢! φ 🡒 ψ → 𝓢 ⊢! χ ▷ φ 🡒 χ ▷ ψ
export HasRule1 (R1!)

section

variable [HasRule1 𝓢]
@[grind ⇐] lemma R1 (h : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ χ ▷ φ 🡒 χ ▷ ψ := ⟨R1! h.some⟩

variable [Entailment.Cl 𝓢]

def R1E! (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! χ ▷ φ 🡘 χ ▷ ψ := K_intro (R1! $ K_left h) (R1! $ K_right h)
@[grind ⇐] lemma R1E (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ χ ▷ φ 🡘 χ ▷ ψ := ⟨R1E! h.some⟩

end


class HasRule2 (𝓢 : S) where
  R2! {φ ψ χ : F} : 𝓢 ⊢! φ 🡒 ψ → 𝓢 ⊢! ψ ▷ χ 🡒 φ ▷ χ
export HasRule2 (R2!)

section

variable [HasRule2 𝓢]

@[grind ⇐] lemma R2 (h : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ψ ▷ χ 🡒 φ ▷ χ := ⟨R2! h.some⟩

variable [Entailment.Cl 𝓢]

def R2E! (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! ψ ▷ χ 🡘 φ ▷ χ := K_intro (R2! $ K_left h) (R2! $ K_right h)
@[grind ⇐] lemma R2E (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ ψ ▷ χ 🡘 φ ▷ χ := ⟨R2E! h.some⟩

end



class HasAxiomJ1 (𝓢 : S) where
  axiomJ1! {φ ψ : F} : 𝓢 ⊢! Axioms.J1 φ ψ
export HasAxiomJ1 (axiomJ1!)

section

variable [HasAxiomJ1 𝓢]

@[simp] lemma axiomJ1 : 𝓢 ⊢ Axioms.J1 φ ψ := ⟨axiomJ1!⟩

variable [ModusPonens 𝓢]

def rhdOfLC! (h : 𝓢 ⊢! □(φ 🡒 ψ)) : 𝓢 ⊢! (φ ▷ ψ) := axiomJ1! ⨀ h

@[grind ⇐]
lemma rhd_of_lc (h : 𝓢 ⊢ □(φ 🡒 ψ)) : 𝓢 ⊢ (φ ▷ ψ) := ⟨rhdOfLC! h.some⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ1 Γ := ⟨λ {_} => of axiomJ1!⟩

open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ1 Γ := ⟨λ {_} => of axiomJ1!⟩

end


class HasAxiomJ1' (𝓢 : S) where
  axiomJ1'! {φ : F} : 𝓢 ⊢! Axioms.J1' φ
export HasAxiomJ1' (axiomJ1'!)

section

variable [HasAxiomJ1' 𝓢]

@[simp] lemma axiomJ1' {φ : F} : 𝓢 ⊢ Axioms.J1' φ := ⟨axiomJ1'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ1' Γ := ⟨λ {_} => of axiomJ1'!⟩

open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ1' Γ := ⟨λ {_} => of axiomJ1'!⟩

end


class HasAxiomJ2 (𝓢 : S) where
  axiomJ2! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2 φ ψ χ
export HasAxiomJ2 (axiomJ2!)


section

variable [HasAxiomJ2 𝓢]

@[simp] lemma axiomJ2 : 𝓢 ⊢ Axioms.J2 φ ψ χ := ⟨axiomJ2!⟩

variable [ModusPonens 𝓢]

def rhdTrans! (h₁ : 𝓢 ⊢! φ ▷ ψ) (h₂ : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ▷ χ) := axiomJ2! ⨀ h₁ ⨀ h₂

@[grind ⇐]
lemma rhd_trans (h₁ : 𝓢 ⊢ φ ▷ ψ) (h₂ : 𝓢 ⊢ ψ ▷ χ) : 𝓢 ⊢ (φ ▷ χ) := ⟨rhdTrans! h₁.some h₂.some⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ2 Γ := ⟨λ {_} => of axiomJ2!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ2 Γ := ⟨λ {_} => of axiomJ2!⟩

end

class HasAxiomJ2Plus (𝓢 : S) where
  axiomJ2Plus! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2Plus φ ψ χ
export HasAxiomJ2Plus (axiomJ2Plus!)

section

variable [HasAxiomJ2Plus 𝓢]
@[simp] lemma axiomJ2Plus : 𝓢 ⊢ Axioms.J2Plus φ ψ χ := ⟨axiomJ2Plus!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ2Plus Γ := ⟨λ {_} => of axiomJ2Plus!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ2Plus Γ := ⟨λ {_} => of axiomJ2Plus!⟩

end


class HasAxiomJ2Plus' (𝓢 : S) where
  axiomJ2Plus'! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J2Plus' φ ψ χ
export HasAxiomJ2Plus' (axiomJ2Plus'!)

section

variable [HasAxiomJ2Plus' 𝓢]
@[simp] lemma axiomJ2Plus' : 𝓢 ⊢ Axioms.J2Plus' φ ψ χ := ⟨axiomJ2Plus'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ2Plus' Γ := ⟨λ {_} => of axiomJ2Plus'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ2Plus' Γ := ⟨λ {_} => of axiomJ2Plus'!⟩

end




class HasAxiomJ3 (𝓢 : S) where
  axiomJ3! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J3 φ ψ χ
export HasAxiomJ3 (axiomJ3!)


section

variable [HasAxiomJ3 𝓢]

@[simp] lemma axiomJ3 : 𝓢 ⊢ Axioms.J3 φ ψ χ := ⟨axiomJ3!⟩

variable [ModusPonens 𝓢]

def rhdDilemma! (h₁ : 𝓢 ⊢! φ ▷ χ) (h₂ : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ⋎ ψ) ▷ χ := axiomJ3! ⨀ h₁ ⨀ h₂

@[grind ⇐]
lemma rhd_dilemma (h₁ : 𝓢 ⊢ φ ▷ χ) (h₂ : 𝓢 ⊢ ψ ▷ χ) : 𝓢 ⊢ (φ ⋎ ψ) ▷ χ := ⟨rhdDilemma! h₁.some h₂.some⟩

end



class HasAxiomJ4 (𝓢 : S) where
  axiomJ4! {φ ψ : F} : 𝓢 ⊢! Axioms.J4 φ ψ
export HasAxiomJ4 (axiomJ4!)

section

variable [HasAxiomJ4 𝓢]

@[simp] lemma axiomJ4 : 𝓢 ⊢ Axioms.J4 φ ψ := ⟨axiomJ4!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4 Γ := ⟨λ {_} => of axiomJ4!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4 Γ := ⟨λ {_} => of axiomJ4!⟩

variable [ModusPonens 𝓢]

def CMM_of_Rhd! (h : 𝓢 ⊢! φ ▷ ψ) : 𝓢 ⊢! (◇φ 🡒 ◇ψ) := axiomJ4! ⨀ h
@[grind ⇐] lemma CMM_of_rhd (h : 𝓢 ⊢ φ ▷ ψ) : 𝓢 ⊢ (◇φ 🡒 ◇ψ) := ⟨CMM_of_Rhd! h.some⟩

end


class HasAxiomJ4' (𝓢 : S) where
  axiomJ4'! {φ ψ : F} : 𝓢 ⊢! Axioms.J4' φ ψ
export HasAxiomJ4' (axiomJ4'!)

section

variable [HasAxiomJ4' 𝓢]

@[simp] lemma axiomJ4' {φ ψ : F} : 𝓢 ⊢ Axioms.J4' φ ψ := ⟨axiomJ4'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4' Γ := ⟨λ {_} => of axiomJ4'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4' Γ := ⟨λ {_} => of axiomJ4'!⟩

end


class HasAxiomJ4Plus (𝓢 : S) where
  axiomJ4Plus! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus φ ψ χ
export HasAxiomJ4Plus (axiomJ4Plus!)

section

variable [HasAxiomJ4Plus 𝓢]
@[simp] lemma axiomJ4Plus : 𝓢 ⊢ Axioms.J4Plus φ ψ χ := ⟨axiomJ4Plus!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus Γ := ⟨λ {_} => of axiomJ4Plus!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus Γ := ⟨λ {_} => of axiomJ4Plus!⟩

end


class HasAxiomJ4Plus' (𝓢 : S) where
  axiomJ4Plus'! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus' φ ψ χ
export HasAxiomJ4Plus' (axiomJ4Plus'!)

section

variable [HasAxiomJ4Plus' 𝓢]
@[simp] lemma axiomJ4Plus' : 𝓢 ⊢ Axioms.J4Plus' φ ψ χ := ⟨axiomJ4Plus'!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus' Γ := ⟨λ {_} => of axiomJ4Plus'!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus' Γ := ⟨λ {_} => of axiomJ4Plus'!⟩

end


class HasAxiomJ4Plus'' (𝓢 : S) where
  axiomJ4Plus''! {φ ψ χ : F} : 𝓢 ⊢! Axioms.J4Plus'' φ ψ χ
export HasAxiomJ4Plus'' (axiomJ4Plus''!)

section

variable [HasAxiomJ4Plus'' 𝓢]
@[simp] lemma axiomJ4Plus'' : 𝓢 ⊢ Axioms.J4Plus'' φ ψ χ := ⟨axiomJ4Plus''!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ4Plus'' Γ := ⟨λ {_} => of axiomJ4Plus''!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ4Plus'' Γ := ⟨λ {_} => of axiomJ4Plus''!⟩

end


class HasAxiomJ5 (𝓢 : S) where
  axiomJ5! {φ : F} : 𝓢 ⊢! Axioms.J5 φ
export HasAxiomJ5 (axiomJ5!)

section

variable [HasAxiomJ5 𝓢]
@[simp] lemma axiomJ5 : 𝓢 ⊢ Axioms.J5 φ := ⟨axiomJ5!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomJ5 Γ := ⟨λ {_} => of axiomJ5!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomJ5 Γ := ⟨λ {_} => of axiomJ5!⟩

end


class HasAxiomJ6 (𝓢 : S) where
  axiomJ6! {φ : F} : 𝓢 ⊢! Axioms.J6 φ
export HasAxiomJ6 (axiomJ6!)

section

variable [HasAxiomJ6 𝓢]

@[simp] lemma axiomJ6 : 𝓢 ⊢ Axioms.J6 φ := ⟨axiomJ6!⟩

variable [Entailment.Cl 𝓢]

def CLRhdNO! : 𝓢 ⊢! □φ 🡒 (∼φ ▷ ⊥) := K_left $ axiomJ6!
@[simp, grind .] lemma CLRhdNO : 𝓢 ⊢ □φ 🡒 (∼φ ▷ ⊥) := ⟨CLRhdNO!⟩

def CRhdNOL! : 𝓢 ⊢! (∼φ ▷ ⊥) 🡒 □φ := K_right $ axiomJ6!
@[simp, grind .] lemma CRhdNOL : 𝓢 ⊢ (∼φ ▷ ⊥) 🡒 □φ := ⟨CRhdNOL!⟩

def NrhdO!_of_L! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! (∼φ ▷ ⊥) := CLRhdNO! ⨀ h
@[grind .] lemma NrhdO_of_L (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ (∼φ ▷ ⊥) := ⟨NrhdO!_of_L! h.some⟩

def L!_of_NrhdO! (h : 𝓢 ⊢! ∼φ ▷ ⊥) : 𝓢 ⊢! □φ := CRhdNOL! ⨀ h
@[grind .] lemma L_of_NrhdO (h : 𝓢 ⊢ ∼φ ▷ ⊥) : 𝓢 ⊢ □φ := ⟨L!_of_NrhdO! h.some⟩

end


class HasAxiomP (𝓢 : S) where
  axiomP! {φ ψ : F} : 𝓢 ⊢! Axioms.P φ ψ
export HasAxiomP (axiomP!)

section

variable [HasAxiomP 𝓢]
@[simp] lemma axiomP : 𝓢 ⊢ Axioms.P φ ψ := ⟨axiomP!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomP Γ := ⟨λ {_} => of axiomP!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomP Γ := ⟨λ {_} => of axiomP!⟩

end


class HasAxiomP₀ (𝓢 : S) where
  axiomP₀! {φ ψ : F} : 𝓢 ⊢! Axioms.P₀ φ ψ
export HasAxiomP₀ (axiomP₀!)
section
variable [HasAxiomP₀ 𝓢]
@[simp] lemma axiomP₀ : 𝓢 ⊢ Axioms.P₀ φ ψ := ⟨axiomP₀!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomP₀ Γ := ⟨λ {_} => of axiomP₀!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomP₀ Γ := ⟨λ {_} => of axiomP₀!⟩
end


class HasAxiomM (𝓢 : S) where
  axiomM! {φ ψ χ : F} : 𝓢 ⊢! Axioms.M φ ψ χ
export HasAxiomM (axiomM!)

section

variable [HasAxiomM 𝓢]
@[simp] lemma axiomM : 𝓢 ⊢ Axioms.M φ ψ χ := ⟨axiomM!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomM Γ := ⟨λ {_} => of axiomM!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomM Γ := ⟨λ {_} => of axiomM!⟩

end


class HasAxiomM₀ (𝓢 : S) where
  axiomM₀! {φ ψ χ : F} : 𝓢 ⊢! Axioms.M₀ φ ψ χ
export HasAxiomM₀ (axiomM₀!)

section
variable [HasAxiomM₀ 𝓢]
@[simp] lemma axiomM₀ : 𝓢 ⊢ Axioms.M₀ φ ψ χ := ⟨axiomM₀!⟩

open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomM₀ Γ := ⟨λ {_} => of axiomM₀!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomM₀ Γ := ⟨λ {_} => of axiomM₀!⟩
end



class HasAxiomKM1 (𝓢 : S) where
  axiomKM1! {φ ψ : F} : 𝓢 ⊢! Axioms.KM1 φ ψ
export HasAxiomKM1 (axiomKM1!)

section
variable [HasAxiomKM1 𝓢]
@[simp] lemma axiomKM1 : 𝓢 ⊢ Axioms.KM1 φ ψ := ⟨axiomKM1!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKM1 Γ := ⟨λ {_} => of axiomKM1!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomKM1 Γ := ⟨λ {_} => of axiomKM1!⟩
end


class HasAxiomW (𝓢 : S) where
  axiomW! {φ ψ : F} : 𝓢 ⊢! Axioms.W φ ψ
export HasAxiomW (axiomW!)

section
variable [HasAxiomW 𝓢]
@[simp] lemma axiomW : 𝓢 ⊢ Axioms.W φ ψ := ⟨axiomW!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomW Γ := ⟨λ {_} => of axiomW!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomW Γ := ⟨λ {_} => of axiomW!⟩
end


class HasAxiomWstar (𝓢 : S) where
  axiomWstar! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Wstar φ ψ χ
export HasAxiomWstar (axiomWstar!)
section
variable [HasAxiomWstar 𝓢]
@[simp] lemma axiomWstar : 𝓢 ⊢ Axioms.Wstar φ ψ χ := ⟨axiomWstar!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomWstar Γ := ⟨λ {_} => of axiomWstar!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomWstar Γ := ⟨λ {_} => of axiomWstar!⟩
end


class HasAxiomKW1Zero (𝓢 : S) where
  axiomKW1Zero! {φ ψ : F} : 𝓢 ⊢! Axioms.KW1Zero φ ψ
export HasAxiomKW1Zero (axiomKW1Zero!)
section
variable [HasAxiomKW1Zero 𝓢]
@[simp] lemma axiomKW1Zero : 𝓢 ⊢ Axioms.KW1Zero φ ψ := ⟨axiomKW1Zero!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKW1Zero Γ := ⟨λ {_} => of axiomKW1Zero!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomKW1Zero Γ := ⟨λ {_} => of axiomKW1Zero!⟩
end


class HasAxiomKW2 (𝓢 : S) where
  axiomKW2! {φ ψ : F} : 𝓢 ⊢! Axioms.KW2 φ ψ
export HasAxiomKW2 (axiomKW2!)
section
variable [HasAxiomKW2 𝓢]
@[simp] lemma axiomKW2 : 𝓢 ⊢ Axioms.KW2 φ ψ := ⟨axiomKW2!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKW2 Γ := ⟨λ {_} => of axiomKW2!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomKW2 Γ := ⟨λ {_} => of axiomKW2!⟩
end


class HasAxiomF (𝓢 : S) where
  axiomF! {φ : F} : 𝓢 ⊢! Axioms.F φ
export HasAxiomF (axiomF!)
section
variable [HasAxiomF 𝓢]
@[simp] lemma axiomF : 𝓢 ⊢ Axioms.F φ := ⟨axiomF!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomF Γ := ⟨λ {_} => of axiomF!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomF Γ := ⟨λ {_} => of axiomF!⟩
end


class HasAxiomR (𝓢 : S) where
  axiomR! {φ ψ χ : F} : 𝓢 ⊢! Axioms.R φ ψ χ
export HasAxiomR (axiomR!)
section
variable [HasAxiomR 𝓢]
@[simp] lemma axiomR : 𝓢 ⊢ Axioms.R φ ψ χ := ⟨axiomR!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomR Γ := ⟨λ {_} => of axiomR!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomR Γ := ⟨λ {_} => of axiomR!⟩
end


class HasAxiomRstar (𝓢 : S) where
  axiomRstar! {φ ψ χ : F} : 𝓢 ⊢! Axioms.Rstar φ ψ χ
export HasAxiomRstar (axiomRstar!)
section
variable [HasAxiomRstar 𝓢]
@[simp] lemma axiomRstar : 𝓢 ⊢ Axioms.Rstar φ ψ χ := ⟨axiomRstar!⟩
open FiniteContext in instance [Entailment.Minimal 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomRstar Γ := ⟨λ {_} => of axiomRstar!⟩
open Context in instance [Entailment.Minimal 𝓢] (Γ : Context F 𝓢) : HasAxiomRstar Γ := ⟨λ {_} => of axiomRstar!⟩
end

end LO.InterpretabilityLogic.Entailment
end

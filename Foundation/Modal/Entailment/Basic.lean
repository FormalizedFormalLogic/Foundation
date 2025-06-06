import Foundation.Logic.Disjunctive
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Entailment.Cl
import Foundation.Modal.Axioms

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S}

class Necessitation (𝓢 : S) where
  nec {φ : F} : 𝓢 ⊢ φ → 𝓢 ⊢ □φ

section

variable [Necessitation 𝓢]
alias nec := Necessitation.nec

lemma nec! : 𝓢 ⊢! φ → 𝓢 ⊢! □φ := by rintro ⟨hp⟩; exact ⟨nec hp⟩

def multinec : 𝓢 ⊢ φ → 𝓢 ⊢ □^[n]φ := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;
lemma multinec! : 𝓢 ⊢! φ → 𝓢 ⊢! □^[n]φ := by rintro ⟨hp⟩; exact ⟨multinec hp⟩

end


class Unnecessitation (𝓢 : S) where
  unnec {φ : F} : 𝓢 ⊢ □φ → 𝓢 ⊢ φ

section

variable [Unnecessitation 𝓢]

alias unnec := Unnecessitation.unnec
lemma unnec! : 𝓢 ⊢! □φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨unnec hp⟩

def multiunnec : 𝓢 ⊢ □^[n]φ → 𝓢 ⊢ φ := by
  intro h;
  induction n generalizing φ with
  | zero => simpa;
  | succ n ih => exact unnec $ @ih (□φ) h;
lemma multiunnec! : 𝓢 ⊢! □^[n]φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨multiunnec hp⟩

end


class LoebRule [LogicalConnective F] (𝓢 : S) where
  loeb {φ : F} : 𝓢 ⊢ □φ ➝ φ → 𝓢 ⊢ φ

section

variable [LoebRule 𝓢]

alias loeb := LoebRule.loeb
lemma loeb! : 𝓢 ⊢! □φ ➝ φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨loeb hp⟩

end


class HenkinRule [LogicalConnective F] (𝓢 : S) where
  henkin {φ : F} : 𝓢 ⊢ □φ ⭤ φ → 𝓢 ⊢ φ

section

variable [HenkinRule 𝓢]

alias henkin := HenkinRule.henkin
lemma henkin! : 𝓢 ⊢! □φ ⭤ φ → 𝓢 ⊢! φ := by rintro ⟨hp⟩; exact ⟨henkin hp⟩

end



class HasDiaDuality (𝓢 : S) where
  dia_dual (φ : F) : 𝓢 ⊢ Axioms.DiaDuality φ

section

variable [HasDiaDuality 𝓢]

def diaDuality : 𝓢 ⊢ ◇φ ⭤ ∼(□(∼φ)) := HasDiaDuality.dia_dual _
@[simp] lemma dia_duality! : 𝓢 ⊢! ◇φ ⭤ ∼(□(∼φ)) := ⟨diaDuality⟩

end



class HasAxiomK [LogicalConnective F] [Box F](𝓢 : S) where
  K (φ ψ : F) : 𝓢 ⊢ Axioms.K φ ψ

section

variable [HasAxiomK 𝓢]

def axiomK : 𝓢 ⊢ □(φ ➝ ψ) ➝ □φ ➝ □ψ := HasAxiomK.K _ _
@[simp] lemma axiomK! : 𝓢 ⊢! □(φ ➝ ψ) ➝ □φ ➝ □ψ := ⟨axiomK⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ FiniteContext.of axiomK⟩
instance (Γ : Context F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ Context.of axiomK⟩

def axiomK' (h : 𝓢 ⊢ □(φ ➝ ψ)) : 𝓢 ⊢ □φ ➝ □ψ := axiomK ⨀ h
@[simp] lemma axiomK'! (h : 𝓢 ⊢! □(φ ➝ ψ)) : 𝓢 ⊢! □φ ➝ □ψ := ⟨axiomK' h.some⟩

def axiomK'' (h₁ : 𝓢 ⊢ □(φ ➝ ψ)) (h₂ : 𝓢 ⊢ □φ) : 𝓢 ⊢ □ψ := axiomK' h₁ ⨀ h₂
@[simp] lemma axiomK''! (h₁ : 𝓢 ⊢! □(φ ➝ ψ)) (h₂ : 𝓢 ⊢! □φ) : 𝓢 ⊢! □ψ := ⟨axiomK'' h₁.some h₂.some⟩

end


class HasAxiomT (𝓢 : S) where
  T (φ : F) : 𝓢 ⊢ Axioms.T φ

section

variable [HasAxiomT 𝓢]

def axiomT : 𝓢 ⊢ □φ ➝ φ := HasAxiomT.T _
@[simp] lemma axiomT! {φ} : 𝓢 ⊢! □φ ➝ φ := ⟨axiomT⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ FiniteContext.of axiomT⟩
instance (Γ : Context F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ Context.of axiomT⟩

def axiomT' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ φ := axiomT ⨀ h
@[simp] lemma axiomT'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! φ := ⟨axiomT' h.some⟩

end

class HasAxiomDiaTc (𝓢 : S) where
  diaTc (φ : F) : 𝓢 ⊢ Axioms.DiaTc φ

section

variable [HasAxiomDiaTc 𝓢]

def diaTc : 𝓢 ⊢ φ ➝ ◇φ := HasAxiomDiaTc.diaTc _
@[simp] lemma diaTc! : 𝓢 ⊢! φ ➝ ◇φ := ⟨diaTc⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ FiniteContext.of diaTc⟩
instance (Γ : Context F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ Context.of diaTc⟩

def diaTc' (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ◇φ := diaTc ⨀ h
lemma diaTc'! (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ◇φ := ⟨diaTc' h.some⟩

end


class HasAxiomD [Dia F] (𝓢 : S) where
  D (φ : F) : 𝓢 ⊢ Axioms.D φ

section

variable [HasAxiomD 𝓢]

def axiomD : 𝓢 ⊢ □φ ➝ ◇φ := HasAxiomD.D _
@[simp] lemma axiomD! : 𝓢 ⊢! □φ ➝ ◇φ := ⟨axiomD⟩


variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ FiniteContext.of axiomD⟩
instance (Γ : Context F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ Context.of axiomD⟩

def axiomD' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ ◇φ := axiomD ⨀ h
lemma axiomD'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! ◇φ := ⟨axiomD' h.some⟩

end



class HasAxiomP (𝓢 : S) where
  P : 𝓢 ⊢ Axioms.P

section

variable [HasAxiomP 𝓢]

def axiomP : 𝓢 ⊢ ∼□⊥  := HasAxiomP.P
@[simp] lemma axiomP! : 𝓢 ⊢! ∼□⊥ := ⟨axiomP⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomP Γ := ⟨FiniteContext.of axiomP⟩
instance (Γ : Context F 𝓢) : HasAxiomP Γ := ⟨Context.of axiomP⟩

end



class HasAxiomB [Dia F] (𝓢 : S) where
  B (φ : F) : 𝓢 ⊢ Axioms.B φ

section

variable [HasAxiomB 𝓢]

def axiomB : 𝓢 ⊢ φ ➝ □◇φ := HasAxiomB.B _
@[simp] lemma axiomB! : 𝓢 ⊢! φ ➝ □◇φ := ⟨axiomB⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ FiniteContext.of axiomB⟩
instance (Γ : Context F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ Context.of axiomB⟩

def axiomB' (h : 𝓢 ⊢ φ) : 𝓢 ⊢ □◇φ := axiomB ⨀ h
@[simp] lemma axiomB'! (h : 𝓢 ⊢! φ) : 𝓢 ⊢! □◇φ := ⟨axiomB' h.some⟩

end


class HasAxiomFour (𝓢 : S) where
  Four (φ : F) : 𝓢 ⊢ Axioms.Four φ

section

variable [HasAxiomFour 𝓢]

def axiomFour : 𝓢 ⊢ □φ ➝ □□φ := HasAxiomFour.Four _
@[simp] lemma axiomFour! : 𝓢 ⊢! □φ ➝ □□φ := ⟨axiomFour⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ FiniteContext.of axiomFour⟩
instance (Γ : Context F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ Context.of axiomFour⟩

def axiomFour' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □□φ := axiomFour ⨀ h
def axiomFour'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □□φ := ⟨axiomFour' h.some⟩

end


class HasAxiomFourN (n) (𝓢 : S) where
  FourN (φ : F) : 𝓢 ⊢ Axioms.FourN n φ

section

variable [HasAxiomFourN n 𝓢]

def axiomFourN : 𝓢 ⊢ □^[n]φ ➝ □^[(n + 1)]φ := by apply HasAxiomFourN.FourN
@[simp] lemma axiomFourN! : 𝓢 ⊢!  □^[n]φ ➝ □^[(n + 1)]φ := ⟨axiomFourN⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFourN n Γ := ⟨fun _ ↦ FiniteContext.of axiomFourN⟩
instance (Γ : Context F 𝓢) : HasAxiomFourN n Γ := ⟨fun _ ↦ Context.of axiomFourN⟩

end


class HasAxiomFive [Dia F] (𝓢 : S) where
  Five (φ : F) : 𝓢 ⊢ Axioms.Five φ

section

variable [HasAxiomFive 𝓢]

def axiomFive : 𝓢 ⊢ ◇φ ➝ □◇φ := HasAxiomFive.Five _
@[simp] lemma axiomFive! : 𝓢 ⊢! ◇φ ➝ □◇φ := ⟨axiomFive⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩
instance (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩

end



class HasAxiomL (𝓢 : S) where
  L (φ : F) : 𝓢 ⊢ Axioms.L φ

section

variable [HasAxiomL 𝓢]

def axiomL : 𝓢 ⊢ □(□φ ➝ φ) ➝ □φ := HasAxiomL.L _
@[simp] lemma axiomL! : 𝓢 ⊢! □(□φ ➝ φ) ➝ □φ := ⟨axiomL⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ FiniteContext.of axiomL⟩
instance (Γ : Context F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ Context.of axiomL⟩

end


class HasAxiomPoint2 [Dia F] (𝓢 : S) where
  Point2 (φ : F) : 𝓢 ⊢ Axioms.Point2 φ

section

variable [HasAxiomPoint2 𝓢]

def axiomPoint2 : 𝓢 ⊢ ◇□φ ➝ □◇φ := HasAxiomPoint2.Point2 _
@[simp] lemma axiomPoint2! : 𝓢 ⊢! ◇□φ ➝ □◇φ := ⟨axiomPoint2⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomPoint2 Γ := ⟨fun _ ↦ FiniteContext.of axiomPoint2⟩
instance (Γ : Context F 𝓢) : HasAxiomPoint2 Γ := ⟨fun _ ↦ Context.of axiomPoint2⟩

end


class HasAxiomWeakPoint2 [Dia F] (𝓢 : S) where
  WeakPoint2 (φ ψ : F) : 𝓢 ⊢ Axioms.WeakPoint2 φ ψ

section

variable [HasAxiomWeakPoint2 𝓢]

def axiomWeakPoint2 : 𝓢 ⊢ ◇(□φ ⋏ ψ) ➝ □(◇φ ⋎ ψ) := HasAxiomWeakPoint2.WeakPoint2 _ _
@[simp] lemma axiomWeakPoint2! : 𝓢 ⊢! ◇(□φ ⋏ ψ) ➝ □(◇φ ⋎ ψ) := ⟨axiomWeakPoint2⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomWeakPoint2 Γ := ⟨fun _ _ ↦ FiniteContext.of axiomWeakPoint2⟩
instance (Γ : Context F 𝓢) : HasAxiomWeakPoint2 Γ := ⟨fun _ _ ↦ Context.of axiomWeakPoint2⟩

end


class HasAxiomPoint3 (𝓢 : S) where
  Point3 (φ ψ : F) : 𝓢 ⊢ Axioms.Point3 φ ψ

section

variable [HasAxiomPoint3 𝓢]

def axiomPoint3 : 𝓢 ⊢ □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ) := HasAxiomPoint3.Point3 _ _
@[simp] lemma axiomPoint3! : 𝓢 ⊢! □(□φ ➝ ψ) ⋎ □(□ψ ➝ φ) := ⟨axiomPoint3⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomPoint3 Γ := ⟨fun _ _ ↦ FiniteContext.of axiomPoint3⟩
instance (Γ : Context F 𝓢) : HasAxiomPoint3 Γ := ⟨fun _ _ ↦ Context.of axiomPoint3⟩

end


class HasAxiomWeakPoint3 [Dia F] (𝓢 : S) where
  WeakPoint3 (φ ψ : F) : 𝓢 ⊢ Axioms.WeakPoint3 φ ψ

section

variable [HasAxiomWeakPoint3 𝓢]

def axiomWeakPoint3 : 𝓢 ⊢ □(⊡φ ➝ ψ) ⋎ □(⊡ψ ➝ φ) := HasAxiomWeakPoint3.WeakPoint3 _ _
@[simp] lemma axiomWeakPoint3! : 𝓢 ⊢! □(⊡φ ➝ ψ) ⋎ □(⊡ψ ➝ φ) := ⟨axiomWeakPoint3⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomWeakPoint3 Γ := ⟨fun _ _ ↦ FiniteContext.of axiomWeakPoint3⟩
instance (Γ : Context F 𝓢) : HasAxiomWeakPoint3 Γ := ⟨fun _ _ ↦ Context.of axiomWeakPoint3⟩

end


class HasAxiomGrz (𝓢 : S) where
  Grz (φ : F) : 𝓢 ⊢ Axioms.Grz φ

section

variable [HasAxiomGrz 𝓢]

def axiomGrz : 𝓢 ⊢ □(□(φ ➝ □φ) ➝ φ) ➝ φ := HasAxiomGrz.Grz _
@[simp] lemma axiomGrz! : 𝓢 ⊢! □(□(φ ➝ □φ) ➝ φ) ➝ φ := ⟨axiomGrz⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ FiniteContext.of axiomGrz⟩
instance (Γ : Context F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ Context.of axiomGrz⟩

end


class HasAxiomTc (𝓢 : S) where
  Tc (φ : F) : 𝓢 ⊢ Axioms.Tc φ

section

variable [HasAxiomTc 𝓢]

def axiomTc : 𝓢 ⊢ φ ➝ □φ := HasAxiomTc.Tc _
@[simp] lemma axiomTc! : 𝓢 ⊢! φ ➝ □φ := ⟨axiomTc⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ FiniteContext.of axiomTc⟩
instance (Γ : Context F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ Context.of axiomTc⟩

end


class HasAxiomDiaT (𝓢 : S) where
  diaT (φ : F) : 𝓢 ⊢ Axioms.DiaT φ

section

variable [HasAxiomDiaT 𝓢]

def diaT : 𝓢 ⊢ ◇φ ➝ φ := HasAxiomDiaT.diaT _
@[simp] lemma diaT! : 𝓢 ⊢! ◇φ ➝ φ := ⟨diaT⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ FiniteContext.of diaT⟩
instance (Γ : Context F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ Context.of diaT⟩

def diaT' (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ φ := diaT ⨀ h
lemma diaT'! (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! φ := ⟨diaT' h.some⟩

end


class HasAxiomVer (𝓢 : S) where
  Ver (φ : F) : 𝓢 ⊢ Axioms.Ver φ

section

variable [HasAxiomVer 𝓢]

def axiomVer : 𝓢 ⊢ □φ := HasAxiomVer.Ver _
@[simp] lemma axiomVer! : 𝓢 ⊢! □φ := ⟨axiomVer⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ FiniteContext.of axiomVer⟩
instance (Γ : Context F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ Context.of axiomVer⟩

end



class HasAxiomH (𝓢 : S) where
  H (φ : F) : 𝓢 ⊢ Axioms.H φ

section

variable [HasAxiomH 𝓢]

def axiomH : 𝓢 ⊢ □(□φ ⭤ φ) ➝ □φ := HasAxiomH.H _
@[simp] lemma axiomH! : 𝓢 ⊢! □(□φ ⭤ φ) ➝ □φ := ⟨axiomH⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ FiniteContext.of axiomH⟩
instance (Γ : Context F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ Context.of axiomH⟩

end



class HasAxiomZ (𝓢 : S) where
  Z (φ : F) : 𝓢 ⊢ Axioms.Z φ

section

variable [HasAxiomZ 𝓢]

def axiomZ : 𝓢 ⊢ □(□φ ➝ φ) ➝ (◇□φ ➝ □φ) := HasAxiomZ.Z _
@[simp] lemma axiomZ! : 𝓢 ⊢! □(□φ ➝ φ) ➝ (◇□φ ➝ □φ) := ⟨axiomZ⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomZ Γ := ⟨fun _ ↦ FiniteContext.of axiomZ⟩
instance (Γ : Context F 𝓢) : HasAxiomZ Γ := ⟨fun _ ↦ Context.of axiomZ⟩

end


class HasAxiomM (𝓢 : S) where
  M (φ : F) : 𝓢 ⊢ Axioms.M φ

section

variable [HasAxiomM 𝓢]

def axiomM : 𝓢 ⊢ □◇φ ➝ ◇□φ := HasAxiomM.M _
@[simp] lemma axiomM! : 𝓢 ⊢! □◇φ ➝ ◇□φ := ⟨axiomM⟩

variable [Entailment.Minimal 𝓢]
instance (Γ : FiniteContext F 𝓢) : HasAxiomM Γ := ⟨fun _ ↦ FiniteContext.of axiomM⟩
instance (Γ : Context F 𝓢) : HasAxiomM Γ := ⟨fun _ ↦ Context.of axiomM⟩

end


class HasAxiomMk [LogicalConnective F] [Box F](𝓢 : S) where
  Mk (φ ψ : F) : 𝓢 ⊢ Axioms.Mk φ ψ

section

variable [HasAxiomMk 𝓢]

def axiomMk : 𝓢 ⊢ □φ ⋏ ψ ➝ ◇(□□φ ⋏ ◇ψ) := HasAxiomMk.Mk _ _
@[simp] lemma axiomMk! : 𝓢 ⊢! □φ ⋏ ψ ➝ ◇(□□φ ⋏ ◇ψ) := ⟨axiomMk⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomMk Γ := ⟨fun _ _ ↦ FiniteContext.of axiomMk⟩
instance (Γ : Context F 𝓢) : HasAxiomMk Γ := ⟨fun _ _ ↦ Context.of axiomMk⟩

end


class HasAxiomGeach [LogicalConnective F] (g) (𝓢 : S) where
  Geach (φ : F) : 𝓢 ⊢ Axioms.Geach g φ

section

instance [Entailment.HasAxiomT 𝓢]      : Entailment.HasAxiomGeach ⟨0, 0, 1, 0⟩ 𝓢 := ⟨fun _ => axiomT⟩
instance [Entailment.HasAxiomB 𝓢]      : Entailment.HasAxiomGeach ⟨0, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomB⟩
instance [Entailment.HasAxiomD 𝓢]      : Entailment.HasAxiomGeach ⟨0, 0, 1, 1⟩ 𝓢 := ⟨fun _ => axiomD⟩
instance [Entailment.HasAxiomFour 𝓢]   : Entailment.HasAxiomGeach ⟨0, 2, 1, 0⟩ 𝓢 := ⟨fun _ => axiomFour⟩
instance [Entailment.HasAxiomFourN n 𝓢] : HasAxiomGeach ⟨0, n + 1, n, 0⟩ 𝓢 := ⟨fun _ ↦ axiomFourN⟩
instance [Entailment.HasAxiomFive 𝓢]   : Entailment.HasAxiomGeach ⟨1, 1, 0, 1⟩ 𝓢 := ⟨fun _ => axiomFive⟩
instance [Entailment.HasAxiomTc 𝓢]     : Entailment.HasAxiomGeach ⟨0, 1, 0, 0⟩ 𝓢 := ⟨fun _ => axiomTc⟩
instance [Entailment.HasAxiomPoint2 𝓢] : Entailment.HasAxiomGeach ⟨1, 1, 1, 1⟩ 𝓢 := ⟨fun _ => axiomPoint2⟩

end

section

variable [HasAxiomGeach g 𝓢]

def axiomGeach : 𝓢 ⊢ ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ) := HasAxiomGeach.Geach _
@[simp] lemma axiomGeach! : 𝓢 ⊢! ◇^[g.i](□^[g.m]φ) ➝ □^[g.j](◇^[g.n]φ) := ⟨axiomGeach⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomGeach g Γ := ⟨fun _ ↦ FiniteContext.of axiomGeach⟩
instance (Γ : Context F 𝓢) : HasAxiomGeach g Γ := ⟨fun _ ↦ Context.of axiomGeach⟩

end


section

variable [BasicModalLogicalConnective F] [DecidableEq F]
variable {φ ψ χ : F} {Γ Δ : List F}
variable {𝓢 : S}

instance [Entailment.Minimal 𝓢] [ModalDeMorgan F] [HasAxiomDNE 𝓢] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, ModalDeMorgan.box, DeMorgan.neg];
  apply E_Id;
⟩

instance [Entailment.Minimal 𝓢] [DiaAbbrev F] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, DiaAbbrev.dia_abbrev];
  apply E_Id;
⟩

instance [ModusPonens 𝓢] [HasAxiomT 𝓢] : Unnecessitation 𝓢 := ⟨by
  intro φ hp;
  exact axiomT ⨀ hp;
⟩

end


section

variable (𝓢 : S)

protected class K extends Entailment.Cl 𝓢, Necessitation 𝓢, HasAxiomK 𝓢, HasDiaDuality 𝓢

protected class KD extends Entailment.K 𝓢, HasAxiomD 𝓢

protected class KP extends Entailment.K 𝓢, HasAxiomP 𝓢

protected class KB extends Entailment.K 𝓢, HasAxiomB 𝓢

protected class KT extends Entailment.K 𝓢, HasAxiomT 𝓢
protected class KT' extends Entailment.K 𝓢, HasAxiomDiaTc 𝓢

protected class KTc extends Entailment.K 𝓢, HasAxiomTc 𝓢
protected class KTc' extends Entailment.K 𝓢, HasAxiomDiaT 𝓢

protected class KTB extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomB 𝓢

protected class KD45 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢

protected class KB4 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFour 𝓢

protected class KB5 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFive 𝓢

protected class KDB extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomB 𝓢

protected class KD4 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢

protected class KD5 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFive 𝓢

protected class K45 extends Entailment.K 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢

protected class KT4B extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢, HasAxiomB 𝓢

protected class Triv extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢
instance [Entailment.Triv 𝓢] : Entailment.KT 𝓢 where
instance [Entailment.Triv 𝓢] : Entailment.KTc 𝓢 where

protected class Ver extends Entailment.K 𝓢, HasAxiomVer 𝓢

protected class KM extends Entailment.K 𝓢, HasAxiomM 𝓢

protected class K4 extends Entailment.K 𝓢, HasAxiomFour 𝓢
protected class K4Point1 extends Entailment.K4 𝓢, HasAxiomM 𝓢
protected class K4Point2 extends Entailment.K4 𝓢, HasAxiomWeakPoint2 𝓢
protected class K4Point3 extends Entailment.K4 𝓢, HasAxiomWeakPoint3 𝓢
protected class KD4Point3Z extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢, HasAxiomWeakPoint3 𝓢, HasAxiomZ 𝓢

protected class K5 extends Entailment.K 𝓢, HasAxiomFive 𝓢

protected class S4 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢
instance [Entailment.S4 𝓢] : Entailment.K4 𝓢 where
instance [Entailment.S4 𝓢] : Entailment.KT 𝓢 where

protected class S4Point1 extends Entailment.S4 𝓢, HasAxiomM 𝓢
protected class S4Point2 extends Entailment.S4 𝓢, HasAxiomPoint2 𝓢
protected class S4Point2Point1 extends Entailment.S4 𝓢, HasAxiomM 𝓢, HasAxiomPoint2 𝓢
protected class S4Point3 extends Entailment.S4 𝓢, HasAxiomPoint3 𝓢

protected class S5 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢
instance [Entailment.S5 𝓢] : Entailment.KT 𝓢 where
instance [Entailment.S5 𝓢] : Entailment.K5 𝓢 where

protected class GL extends Entailment.K 𝓢, HasAxiomL 𝓢
protected class GLPoint2 extends Entailment.GL 𝓢, HasAxiomWeakPoint2 𝓢
protected class GLPoint3 extends Entailment.GL 𝓢, HasAxiomWeakPoint3 𝓢

protected class Grz extends Entailment.K 𝓢, HasAxiomGrz 𝓢

protected class KTMk (𝓢 : S) extends Entailment.KT 𝓢, Entailment.HasAxiomMk 𝓢

end


section

class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive : ∀ {φ ψ : F}, 𝓢 ⊢! □φ ⋎ □ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias modal_disjunctive := ModalDisjunctive.modal_disjunctive

variable {𝓢 : S} [Entailment.Minimal 𝓢]

instance [Disjunctive 𝓢] [Unnecessitation 𝓢] : ModalDisjunctive 𝓢 where
  modal_disjunctive h := by
    rcases disjunctive h with (h | h);
    . left; exact unnec! h;
    . right; exact unnec! h;

private lemma unnec_of_mdp_aux [ModalDisjunctive 𝓢] (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! φ := by
    have : 𝓢 ⊢! □φ ⋎ □φ := A!_intro_left h;
    rcases modal_disjunctive this with (h | h) <;> tauto;

noncomputable instance unnecessitation_of_modalDisjunctive [ModalDisjunctive 𝓢] : Unnecessitation 𝓢 where
  unnec h := (unnec_of_mdp_aux ⟨h⟩).some

end

end LO.Modal.Entailment

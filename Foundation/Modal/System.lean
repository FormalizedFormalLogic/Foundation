import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Modal.Axioms

namespace LO.System

variable {S F : Type*} [LogicalConnective F] [System F S]
variable {𝓢 : S}


class Necessitation [Box F] (𝓢 : S) where
  nec {p : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

omit [LogicalConnective F] in
section

variable [Box F] [Necessitation 𝓢]
alias nec := Necessitation.nec

lemma nec! : 𝓢 ⊢! p → 𝓢 ⊢! □p := by rintro ⟨hp⟩; exact ⟨nec hp⟩

def multinec : 𝓢 ⊢ p → 𝓢 ⊢ □^[n]p := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;
lemma multinec! : 𝓢 ⊢! p → 𝓢 ⊢! □^[n]p := by rintro ⟨hp⟩; exact ⟨multinec hp⟩

end


class Unnecessitation [Box F] (𝓢 : S) where
  unnec {p : F} : 𝓢 ⊢ □p → 𝓢 ⊢ p

omit [LogicalConnective F] in
section

variable [Box F] [Unnecessitation 𝓢]

alias unnec := Unnecessitation.unnec
lemma unnec! : 𝓢 ⊢! □p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨unnec hp⟩

def multiunnec : 𝓢 ⊢ □^[n]p → 𝓢 ⊢ p := by
  intro h;
  induction n generalizing p with
  | zero => simpa;
  | succ n ih => exact unnec $ @ih (□p) h;
lemma multiunnec! : 𝓢 ⊢! □^[n]p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨multiunnec hp⟩

end


class LoebRule [LogicalConnective F] [Box F] (𝓢 : S) where
  loeb {p : F} : 𝓢 ⊢ □p ➝ p → 𝓢 ⊢ p

section

variable [Box F] [LoebRule 𝓢]

alias loeb := LoebRule.loeb
lemma loeb! : 𝓢 ⊢! □p ➝ p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨loeb hp⟩

end


class HenkinRule [LogicalConnective F] [Box F] (𝓢 : S) where
  henkin {p : F} : 𝓢 ⊢ □p ⭤ p → 𝓢 ⊢ p

section

variable [Box F] [HenkinRule 𝓢]

alias henkin := HenkinRule.henkin
lemma henkin! : 𝓢 ⊢! □p ⭤ p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨henkin hp⟩

end



class HasDiaDuality [Box F] [Dia F] (𝓢 : S) where
  dia_dual (p : F) : 𝓢 ⊢ Axioms.DiaDuality p

section

variable [Box F] [Dia F] [HasDiaDuality 𝓢]

def diaDuality : 𝓢 ⊢ ◇p ⭤ ∼(□(∼p)) := HasDiaDuality.dia_dual _
@[simp] lemma dia_duality! : 𝓢 ⊢! ◇p ⭤ ∼(□(∼p)) := ⟨diaDuality⟩

end



class HasAxiomK  [LogicalConnective F] [Box F](𝓢 : S) where
  K (p q : F) : 𝓢 ⊢ Axioms.K p q

section

variable [Box F] [HasAxiomK 𝓢]

def axiomK : 𝓢 ⊢ □(p ➝ q) ➝ □p ➝ □q := HasAxiomK.K _ _
@[simp] lemma axiomK! : 𝓢 ⊢! □(p ➝ q) ➝ □p ➝ □q := ⟨axiomK⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ FiniteContext.of axiomK⟩
instance [System.Minimal 𝓢] [HasAxiomK 𝓢] (Γ : Context F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ Context.of axiomK⟩

def axiomK' (h : 𝓢 ⊢ □(p ➝ q)) : 𝓢 ⊢ □p ➝ □q := axiomK ⨀ h
@[simp] lemma axiomK'! (h : 𝓢 ⊢! □(p ➝ q)) : 𝓢 ⊢! □p ➝ □q := ⟨axiomK' h.some⟩

def axiomK'' (h₁ : 𝓢 ⊢ □(p ➝ q)) (h₂ : 𝓢 ⊢ □p) : 𝓢 ⊢ □q := axiomK' h₁ ⨀ h₂
@[simp] lemma axiomK''! (h₁ : 𝓢 ⊢! □(p ➝ q)) (h₂ : 𝓢 ⊢! □p) : 𝓢 ⊢! □q := ⟨axiomK'' h₁.some h₂.some⟩

end


class HasAxiomT [Box F] (𝓢 : S) where
  T (p : F) : 𝓢 ⊢ Axioms.T p

section

variable [Box F] [HasAxiomT 𝓢]

def axiomT : 𝓢 ⊢ □p ➝ p := HasAxiomT.T _
@[simp] lemma axiomT! : 𝓢 ⊢! □p ➝ p := ⟨axiomT⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ FiniteContext.of axiomT⟩
instance (Γ : Context F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ Context.of axiomT⟩

def axiomT' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ p := axiomT ⨀ h
@[simp] lemma axiomT'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! p := ⟨axiomT' h.some⟩

end


class HasAxiomD [Box F] [Dia F] (𝓢 : S) where
  D (p : F) : 𝓢 ⊢ Axioms.D p

section

variable [Box F] [Dia F] [HasAxiomD 𝓢]

def axiomD : 𝓢 ⊢ □p ➝ ◇p := HasAxiomD.D _
@[simp] lemma axiomD! : 𝓢 ⊢! □p ➝ ◇p := ⟨axiomD⟩


variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ FiniteContext.of axiomD⟩
instance (Γ : Context F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ Context.of axiomD⟩

def axiomD' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ ◇p := axiomD ⨀ h
lemma axiomD'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! ◇p := ⟨axiomD' h.some⟩

end



class HasAxiomP [Box F] (𝓢 : S) where
  P : 𝓢 ⊢ Axioms.P

section

variable [Box F] [HasAxiomP 𝓢]

def axiomP : 𝓢 ⊢ ∼□⊥  := HasAxiomP.P
@[simp] lemma axiomP! : 𝓢 ⊢! ∼□⊥ := ⟨axiomP⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomP Γ := ⟨FiniteContext.of axiomP⟩
instance (Γ : Context F 𝓢) : HasAxiomP Γ := ⟨Context.of axiomP⟩

end



class HasAxiomB [Box F] [Dia F] (𝓢 : S) where
  B (p : F) : 𝓢 ⊢ Axioms.B p

section

variable [Box F] [Dia F] [HasAxiomB 𝓢]

def axiomB : 𝓢 ⊢ p ➝ □◇p := HasAxiomB.B _
@[simp] lemma axiomB! : 𝓢 ⊢! p ➝ □◇p := ⟨axiomB⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ FiniteContext.of axiomB⟩
instance (Γ : Context F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ Context.of axiomB⟩

def axiomB' (h : 𝓢 ⊢ p) : 𝓢 ⊢ □◇p := axiomB ⨀ h
@[simp] lemma axiomB'! (h : 𝓢 ⊢! p) : 𝓢 ⊢! □◇p := ⟨axiomB' h.some⟩

end


class HasAxiomFour [Box F] (𝓢 : S) where
  Four (p : F) : 𝓢 ⊢ Axioms.Four p

section

variable [Box F] [HasAxiomFour 𝓢]

def axiomFour : 𝓢 ⊢ □p ➝ □□p := HasAxiomFour.Four _
@[simp] lemma axiomFour! : 𝓢 ⊢! □p ➝ □□p := ⟨axiomFour⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ FiniteContext.of axiomFour⟩
instance (Γ : Context F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ Context.of axiomFour⟩

def axiomFour' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ □□p := axiomFour ⨀ h
def axiomFour'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! □□p := ⟨axiomFour' h.some⟩

end


class HasAxiomFive [Box F] [Dia F] (𝓢 : S) where
  Five (p : F) : 𝓢 ⊢ Axioms.Five p

section

variable [Box F] [Dia F] [HasAxiomFive 𝓢]

def axiomFive : 𝓢 ⊢ ◇p ➝ □◇p := HasAxiomFive.Five _
@[simp] lemma axiomFive! : 𝓢 ⊢! ◇p ➝ □◇p := ⟨axiomFive⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩
instance (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩

end



class HasAxiomL [Box F] (𝓢 : S) where
  L (p : F) : 𝓢 ⊢ Axioms.L p

section

variable [Box F] [HasAxiomL 𝓢]

def axiomL : 𝓢 ⊢ □(□p ➝ p) ➝ □p := HasAxiomL.L _
@[simp] lemma axiomL! : 𝓢 ⊢! □(□p ➝ p) ➝ □p := ⟨axiomL⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ FiniteContext.of axiomL⟩
instance (Γ : Context F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ Context.of axiomL⟩

end


class HasAxiomDot2 [Box F] [Dia F] (𝓢 : S) where
  Dot2 (p : F) : 𝓢 ⊢ Axioms.Dot2 p

class HasAxiomDot3 [Box F] (𝓢 : S) where
  Dot3 (p q : F) : 𝓢 ⊢ Axioms.Dot3 p q


class HasAxiomGrz [Box F] (𝓢 : S) where
  Grz (p : F) : 𝓢 ⊢ Axioms.Grz p

section

variable [Box F] [HasAxiomGrz 𝓢]

def axiomGrz : 𝓢 ⊢ □(□(p ➝ □p) ➝ p) ➝ p := HasAxiomGrz.Grz _
@[simp] lemma axiomGrz! : 𝓢 ⊢! □(□(p ➝ □p) ➝ p) ➝ p := ⟨axiomGrz⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ FiniteContext.of axiomGrz⟩
instance (Γ : Context F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ Context.of axiomGrz⟩

end


class HasAxiomTc [Box F] (𝓢 : S) where
  Tc (p : F) : 𝓢 ⊢ Axioms.Tc p

section

variable [Box F] [HasAxiomTc 𝓢]

def axiomTc : 𝓢 ⊢ p ➝ □p := HasAxiomTc.Tc _
@[simp] lemma axiomTc! : 𝓢 ⊢! p ➝ □p := ⟨axiomTc⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ FiniteContext.of axiomTc⟩
instance (Γ : Context F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ Context.of axiomTc⟩

end



class HasAxiomVer [Box F] (𝓢 : S) where
  Ver (p : F) : 𝓢 ⊢ Axioms.Ver p

omit [LogicalConnective F] in
section

variable [Box F] [HasAxiomVer 𝓢]

def axiomVer : 𝓢 ⊢ □p := HasAxiomVer.Ver _
@[simp] lemma axiomVer! : 𝓢 ⊢! □p := ⟨axiomVer⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ FiniteContext.of axiomVer⟩
instance (Γ : Context F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ Context.of axiomVer⟩

end



class HasAxiomH [Box F] (𝓢 : S) where
  H (p : F) : 𝓢 ⊢ Axioms.H p

section

variable [Box F] [HasAxiomH 𝓢]

def axiomH : 𝓢 ⊢ □(□p ⭤ p) ➝ □p := HasAxiomH.H _
@[simp] lemma axiomH! : 𝓢 ⊢! □(□p ⭤ p) ➝ □p := ⟨axiomH⟩

variable [System.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ FiniteContext.of axiomH⟩
instance (Γ : Context F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ Context.of axiomH⟩

end


section

variable [BasicModalLogicalConnective F]
variable (𝓢 : S)

protected class K extends System.Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢, HasDiaDuality 𝓢

protected class KT extends System.K 𝓢, HasAxiomT 𝓢

protected class KB extends System.K 𝓢, HasAxiomB 𝓢

protected class KTc extends System.K 𝓢, HasAxiomTc 𝓢

protected class KD extends System.K 𝓢, HasAxiomD 𝓢

protected class KP extends System.K 𝓢, HasAxiomP 𝓢

protected class K4 extends System.K 𝓢, HasAxiomFour 𝓢

protected class K5 extends System.K 𝓢, HasAxiomFive 𝓢

protected class S4 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢
instance [System.S4 𝓢] : System.KT 𝓢 where
instance [System.S4 𝓢] : System.K4 𝓢 where

protected class S5 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢
instance [System.S5 𝓢] : System.KT 𝓢 where
instance [System.S5 𝓢] : System.K5 𝓢 where

protected class S4Dot2 extends System.S4 𝓢, HasAxiomDot2 𝓢

protected class S4Dot3 extends System.S4 𝓢, HasAxiomDot3 𝓢

protected class S4Grz extends System.S4 𝓢, HasAxiomGrz 𝓢

protected class S5Grz extends System.S5 𝓢, HasAxiomGrz 𝓢

protected class GL extends System.K 𝓢, HasAxiomL 𝓢

protected class Grz extends System.K 𝓢, HasAxiomGrz 𝓢

protected class Triv extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢
instance [System.Triv 𝓢] : System.KT 𝓢 where
instance [System.Triv 𝓢] : System.KTc 𝓢 where

protected class Ver extends System.K 𝓢, HasAxiomVer 𝓢

protected class K4H extends System.K4 𝓢, HasAxiomH 𝓢

protected class K4Loeb extends System.K4 𝓢, LoebRule 𝓢

protected class K4Henkin extends System.K4 𝓢, HenkinRule 𝓢

end


section

variable [BasicModalLogicalConnective F] [DecidableEq F]
variable {p q r : F} {Γ Δ : List F}
variable {𝓢 : S}

instance [System.Minimal 𝓢] [ModalDeMorgan F] [HasAxiomDNE 𝓢] : HasDiaDuality 𝓢 := ⟨by
  intro p;
  simp only [Axioms.DiaDuality, ModalDeMorgan.box, DeMorgan.neg];
  apply iffId;
⟩

instance [System.Minimal 𝓢] [DiaAbbrev F] : HasDiaDuality 𝓢 := ⟨by
  intro p;
  simp only [Axioms.DiaDuality, DiaAbbrev.dia_abbrev];
  apply iffId;
⟩

instance [ModusPonens 𝓢] [HasAxiomT 𝓢] : Unnecessitation 𝓢 := ⟨by
  intro p hp;
  exact axiomT ⨀ hp;
⟩


open FiniteContext

section K

variable [System.K 𝓢]

def multibox_axiomK : 𝓢 ⊢ □^[n](p ➝ q) ➝ □^[n]p ➝ □^[n]q := by
  induction n with
  | zero => simp; apply impId;
  | succ n ih => simpa using impTrans'' (axiomK' $ nec ih) (by apply axiomK);
@[simp] lemma multibox_axiomK! : 𝓢 ⊢! □^[n](p ➝ q) ➝ □^[n]p ➝ □^[n]q := ⟨multibox_axiomK⟩

def multibox_axiomK' (h : 𝓢 ⊢ □^[n](p ➝ q)) : 𝓢 ⊢ □^[n]p ➝ □^[n]q := multibox_axiomK ⨀ h
@[simp] lemma multibox_axiomK'! (h : 𝓢 ⊢! □^[n](p ➝ q)) : 𝓢 ⊢! □^[n]p ➝ □^[n]q := ⟨multibox_axiomK' h.some⟩

alias multiboxedImplyDistribute := multibox_axiomK'
alias multiboxed_imply_distribute! := multibox_axiomK'!


def boxIff' (h : 𝓢 ⊢ p ⭤ q) : 𝓢 ⊢ (□p ⭤ □q) := by
  apply iffIntro;
  . exact axiomK' $ nec $ and₁' h;
  . exact axiomK' $ nec $ and₂' h;
@[simp] lemma box_iff! (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! □p ⭤ □q := ⟨boxIff' h.some⟩

def multiboxIff' (h : 𝓢 ⊢ p ⭤ q) : 𝓢 ⊢ □^[n]p ⭤ □^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
@[simp] lemma multibox_iff! (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! □^[n]p ⭤ □^[n]q := ⟨multiboxIff' h.some⟩


def diaDuality_mp : 𝓢 ⊢ ◇p ➝ ∼(□(∼p)) := and₁' diaDuality
@[simp] lemma diaDuality_mp! : 𝓢 ⊢! ◇p ➝ ∼(□(∼p)) := ⟨diaDuality_mp⟩

def diaDuality_mpr : 𝓢 ⊢ ∼(□(∼p)) ➝ ◇p := and₂' diaDuality
@[simp] lemma diaDuality_mpr! : 𝓢 ⊢! ∼(□(∼p)) ➝ ◇p := ⟨diaDuality_mpr⟩

def diaDuality'.mp (h : 𝓢 ⊢ ◇p) : 𝓢 ⊢ ∼(□(∼p)) := (and₁' diaDuality) ⨀ h
def diaDuality'.mpr (h : 𝓢 ⊢ ∼(□(∼p))) : 𝓢 ⊢ ◇p := (and₂' diaDuality) ⨀ h

lemma dia_duality'! : 𝓢 ⊢! ◇p ↔ 𝓢 ⊢! ∼(□(∼p)) := ⟨
  λ h => ⟨diaDuality'.mp h.some⟩,
  λ h => ⟨diaDuality'.mpr h.some⟩
⟩

def multiDiaDuality : 𝓢 ⊢ ◇^[n]p ⭤ ∼(□^[n](∼p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp;
    apply iffTrans'' $ diaDuality (p := ◇^[n]p);
    apply negReplaceIff';
    apply boxIff';
    apply iffIntro;
    . exact contra₂' $ and₂' ih;
    . exact contra₁' $ and₁' ih;
lemma multidia_duality! : 𝓢 ⊢! ◇^[n]p ⭤ ∼(□^[n](∼p)) := ⟨multiDiaDuality⟩

lemma multidia_duality'! : 𝓢 ⊢! ◇^[n]p ↔ 𝓢 ⊢! ∼(□^[n](∼p)) := by
  constructor;
  . intro h; exact (and₁'! multidia_duality!) ⨀ h;
  . intro h; exact (and₂'! multidia_duality!) ⨀ h;

def diaIff' (h : 𝓢 ⊢ p ⭤ q) : 𝓢 ⊢ (◇p ⭤ ◇q) := by
  apply iffTrans'' diaDuality;
  apply andComm';
  apply iffTrans'' diaDuality;
  apply negReplaceIff';
  apply boxIff';
  apply negReplaceIff';
  apply andComm';
  assumption;

@[simp] lemma dia_iff! (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! ◇p ⭤ ◇q := ⟨diaIff' h.some⟩

def multidiaIff' (h : 𝓢 ⊢ p ⭤ q) : 𝓢 ⊢ ◇^[n]p ⭤ ◇^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
@[simp] lemma multidia_iff! (h : 𝓢 ⊢! p ⭤ q) : 𝓢 ⊢! ◇^[n]p ⭤ ◇^[n]q := ⟨multidiaIff' h.some⟩

def multiboxDuality : 𝓢 ⊢ □^[n]p ⭤ ∼(◇^[n](∼p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp;
    apply iffTrans'' (boxIff' ih);
    apply iffNegRightToLeft';
    exact iffComm' $ diaDuality;

@[simp] lemma multibox_duality! : 𝓢 ⊢! □^[n]p ⭤ ∼(◇^[n](∼p)) := ⟨multiboxDuality⟩

def boxDuality : 𝓢 ⊢ □p ⭤ ∼(◇(∼p)) := multiboxDuality (n := 1)
@[simp] lemma box_duality! : 𝓢 ⊢! □p ⭤ ∼(◇(∼p)) := ⟨boxDuality⟩

def boxDuality_mp : 𝓢 ⊢ □p ➝ ∼(◇(∼p)) := and₁' boxDuality
@[simp] lemma boxDuality_mp! : 𝓢 ⊢! □p ➝ ∼(◇(∼p)) := ⟨boxDuality_mp⟩

def boxDuality_mp' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ ∼(◇(∼p)) := boxDuality_mp ⨀ h
lemma boxDuality_mp'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! ∼(◇(∼p)) := ⟨boxDuality_mp' h.some⟩

def boxDuality_mpr : 𝓢 ⊢ ∼(◇(∼p)) ➝ □p := and₂' boxDuality
@[simp] lemma boxDuality_mpr! : 𝓢 ⊢! ∼(◇(∼p)) ➝ □p := ⟨boxDuality_mpr⟩

def boxDuality_mpr' (h : 𝓢 ⊢ ∼(◇(∼p))) : 𝓢 ⊢ □p := boxDuality_mpr ⨀ h
lemma boxDuality_mpr'! (h : 𝓢 ⊢! ∼(◇(∼p))) : 𝓢 ⊢! □p := ⟨boxDuality_mpr' h.some⟩

lemma multibox_duality'! : 𝓢 ⊢! □^[n]p ↔ 𝓢 ⊢! ∼(◇^[n](∼p)) := by
  constructor;
  . intro h; exact (and₁'! multibox_duality!) ⨀ h;
  . intro h; exact (and₂'! multibox_duality!) ⨀ h;

lemma box_duality'! : 𝓢 ⊢! □p ↔ 𝓢 ⊢! ∼(◇(∼p)) := multibox_duality'! (n := 1)

def box_dne : 𝓢 ⊢ □(∼∼p) ➝ □p := axiomK' $ nec dne
@[simp] lemma box_dne! : 𝓢 ⊢! □(∼∼p) ➝ □p := ⟨box_dne⟩

def box_dne' (h : 𝓢 ⊢ □(∼∼p)): 𝓢 ⊢ □p := box_dne ⨀ h
lemma box_dne'! (h : 𝓢 ⊢! □(∼∼p)): 𝓢 ⊢! □p := ⟨box_dne' h.some⟩


def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
@[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := ⟨multiboxverum⟩

def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
@[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := ⟨boxverum⟩

def boxdotverum : 𝓢 ⊢ (⊡⊤ : F) := andIntro verum boxverum
@[simp] lemma boxdotverum! : 𝓢 ⊢! (⊡⊤ : F) := ⟨boxdotverum⟩

def implyMultiboxDistribute' (h : 𝓢 ⊢ p ➝ q) : 𝓢 ⊢ □^[n]p ➝ □^[n]q := multibox_axiomK' $ multinec h
lemma imply_multibox_distribute'! (h : 𝓢 ⊢! p ➝ q) : 𝓢 ⊢! □^[n]p ➝ □^[n]q := ⟨implyMultiboxDistribute' h.some⟩

def implyBoxDistribute' (h : 𝓢 ⊢ p ➝ q) : 𝓢 ⊢ □p ➝ □q := implyMultiboxDistribute' (n := 1) h
lemma imply_box_distribute'! (h : 𝓢 ⊢! p ➝ q) : 𝓢 ⊢! □p ➝ □q := ⟨implyBoxDistribute' h.some⟩


def distribute_multibox_and : 𝓢 ⊢ □^[n](p ⋏ q) ➝ □^[n]p ⋏ □^[n]q := implyRightAnd (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)
@[simp] lemma distribute_multibox_and! : 𝓢 ⊢! □^[n](p ⋏ q) ➝ □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and⟩

def distribute_box_and : 𝓢 ⊢ □(p ⋏ q) ➝ □p ⋏ □q := distribute_multibox_and (n := 1)
@[simp] lemma distribute_box_and! : 𝓢 ⊢! □(p ⋏ q) ➝ □p ⋏ □q := ⟨distribute_box_and⟩

def distribute_multibox_and' (h : 𝓢 ⊢ □^[n](p ⋏ q)) : 𝓢 ⊢ □^[n]p ⋏ □^[n]q := distribute_multibox_and ⨀ h
lemma distribute_multibox_and'! (d : 𝓢 ⊢! □^[n](p ⋏ q)) : 𝓢 ⊢! □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and' d.some⟩

def distribute_box_and' (h : 𝓢 ⊢ □(p ⋏ q)) : 𝓢 ⊢ □p ⋏ □q := distribute_multibox_and' (n := 1) h
lemma distribute_box_and'! (d : 𝓢 ⊢! □(p ⋏ q)) : 𝓢 ⊢! □p ⋏ □q := ⟨distribute_box_and' d.some⟩

lemma conj_cons! : 𝓢 ⊢! (p ⋏ ⋀Γ) ⭤ ⋀(p :: Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil =>
    simp;
    apply iff_intro!;
    . simp;
    . exact imply_right_and! (by simp) (by simp);
  | _ => simp;

@[simp]
lemma distribute_multibox_conj! : 𝓢 ⊢! □^[n]⋀Γ ➝ ⋀□'^[n]Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons p Γ h ih =>
    simp_all;
    have h₁ : 𝓢 ⊢! □^[n](p ⋏ ⋀Γ) ➝ □^[n]p := imply_multibox_distribute'! $ and₁!;
    have h₂ : 𝓢 ⊢! □^[n](p ⋏ ⋀Γ) ➝ ⋀□'^[n]Γ := imp_trans''! (imply_multibox_distribute'! $ and₂!) ih;
    have := imply_right_and! h₁ h₂;
    exact imp_trans''! this $ by
      apply imply_conj'!;
      intro q hq;
      simp at hq;
      rcases hq with (rfl | ⟨q, hq, rfl⟩)
      . apply and₁!;
      . suffices 𝓢 ⊢! ⋀□'^[n]Γ ➝ □^[n]q by exact dhyp_and_left! this;
        apply generate_conj'!;
        simpa;

@[simp] lemma distribute_box_conj! : 𝓢 ⊢! □(⋀Γ) ➝ ⋀(□'Γ) := distribute_multibox_conj! (n := 1)

def collect_multibox_and : 𝓢 ⊢ □^[n]p ⋏ □^[n]q ➝ □^[n](p ⋏ q) := by
  have d₁ : 𝓢 ⊢ □^[n]p ➝ □^[n](q ➝ p ⋏ q) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](q ➝ p ⋏ q) ➝ (□^[n]q ➝ □^[n](p ⋏ q)) := multibox_axiomK;
  exact (and₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans'' d₁ d₂);
@[simp] lemma collect_multibox_and! : 𝓢 ⊢! □^[n]p ⋏ □^[n]q ➝ □^[n](p ⋏ q) := ⟨collect_multibox_and⟩

def collect_box_and : 𝓢 ⊢ □p ⋏ □q ➝ □(p ⋏ q) := collect_multibox_and (n := 1)
@[simp] lemma collect_box_and! : 𝓢 ⊢! □p ⋏ □q ➝ □(p ⋏ q) := ⟨collect_box_and⟩

def collect_multibox_and' (h : 𝓢 ⊢ □^[n]p ⋏ □^[n]q) : 𝓢 ⊢ □^[n](p ⋏ q) := collect_multibox_and ⨀ h
lemma collect_multibox_and'! (h : 𝓢 ⊢! □^[n]p ⋏ □^[n]q) : 𝓢 ⊢! □^[n](p ⋏ q) := ⟨collect_multibox_and' h.some⟩

def collect_box_and' (h : 𝓢 ⊢ □p ⋏ □q) : 𝓢 ⊢ □(p ⋏ q) := collect_multibox_and' (n := 1) h
lemma collect_box_and'! (h : 𝓢 ⊢! □p ⋏ □q) : 𝓢 ⊢! □(p ⋏ q) := ⟨collect_box_and' h.some⟩


lemma multiboxConj'_iff! : 𝓢 ⊢! □^[n]⋀Γ ↔ ∀ p ∈ Γ, 𝓢 ⊢! □^[n]p := by
  induction Γ using List.induction_with_singleton with
  | hcons p Γ h ih =>
    simp_all;
    constructor;
    . intro h;
      have := distribute_multibox_and'! h;
      constructor;
      . exact and₁'! this;
      . exact ih.mp (and₂'! this);
    . rintro ⟨h₁, h₂⟩;
      exact collect_multibox_and'! $ and₃'! h₁ (ih.mpr h₂);
  | _ => simp_all;
lemma boxConj'_iff! : 𝓢 ⊢! □⋀Γ ↔ ∀ p ∈ Γ, 𝓢 ⊢! □p := multiboxConj'_iff! (n := 1)

lemma multiboxconj_of_conjmultibox! (d : 𝓢 ⊢! ⋀□'^[n]Γ) : 𝓢 ⊢! □^[n]⋀Γ := by
  apply multiboxConj'_iff!.mpr;
  intro p hp;
  exact iff_provable_list_conj.mp d (□^[n]p) (by aesop);

@[simp]
lemma multibox_cons_conjAux₁! :  𝓢 ⊢! ⋀(□'^[n](p :: Γ)) ➝ ⋀□'^[n]Γ := by
  apply conjconj_subset!;
  simp_all;

@[simp]
lemma multibox_cons_conjAux₂! :  𝓢 ⊢! ⋀(□'^[n](p :: Γ)) ➝ □^[n]p := by
  suffices 𝓢 ⊢! ⋀(□'^[n](p :: Γ)) ➝ ⋀□'^[n]([p]) by simpa;
  apply conjconj_subset!;
  simp_all;


@[simp]
lemma multibox_cons_conj! :  𝓢 ⊢! ⋀(□'^[n](p :: Γ)) ➝ ⋀□'^[n]Γ ⋏ □^[n]p :=
  imply_right_and! multibox_cons_conjAux₁! multibox_cons_conjAux₂!

@[simp]
lemma collect_multibox_conj! : 𝓢 ⊢! ⋀□'^[n]Γ ➝ □^[n]⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using dhyp! multiboxverum!;
  | hsingle => simp;
  | hcons p Γ h ih =>
    simp_all;
    exact imp_trans''! (imply_right_and! (generalConj'! (by simp)) (imp_trans''! (by simp) ih)) collect_multibox_and!;

@[simp]
lemma collect_box_conj! : 𝓢 ⊢! ⋀(□'Γ) ➝ □(⋀Γ) := collect_multibox_conj! (n := 1)


def collect_multibox_or : 𝓢 ⊢ □^[n]p ⋎ □^[n]q ➝ □^[n](p ⋎ q) := or₃'' (multibox_axiomK' $ multinec or₁) (multibox_axiomK' $ multinec or₂)
@[simp] lemma collect_multibox_or! : 𝓢 ⊢! □^[n]p ⋎ □^[n]q ➝ □^[n](p ⋎ q) := ⟨collect_multibox_or⟩

def collect_box_or : 𝓢 ⊢ □p ⋎ □q ➝ □(p ⋎ q) := collect_multibox_or (n := 1)
@[simp] lemma collect_box_or! : 𝓢 ⊢! □p ⋎ □q ➝ □(p ⋎ q) := ⟨collect_box_or⟩

def collect_multibox_or' (h : 𝓢 ⊢ □^[n]p ⋎ □^[n]q) : 𝓢 ⊢ □^[n](p ⋎ q) := collect_multibox_or ⨀ h
lemma collect_multibox_or'! (h : 𝓢 ⊢! □^[n]p ⋎ □^[n]q) : 𝓢 ⊢! □^[n](p ⋎ q) := ⟨collect_multibox_or' h.some⟩

def collect_box_or' (h : 𝓢 ⊢ □p ⋎ □q) : 𝓢 ⊢ □(p ⋎ q) := collect_multibox_or' (n := 1) h
lemma collect_box_or'! (h : 𝓢 ⊢! □p ⋎ □q) : 𝓢 ⊢! □(p ⋎ q) := ⟨collect_box_or' h.some⟩

def diaOrInst₁ : 𝓢 ⊢ ◇p ➝ ◇(p ⋎ q) := by
  apply impTrans'' (and₁' diaDuality);
  apply impTrans'' ?h (and₂' diaDuality);
  apply contra₀';
  apply axiomK';
  apply nec;
  apply contra₀';
  exact or₁;
@[simp] lemma dia_or_inst₁! : 𝓢 ⊢! ◇p ➝ ◇(p ⋎ q) := ⟨diaOrInst₁⟩

def diaOrInst₂ : 𝓢 ⊢ ◇q ➝ ◇(p ⋎ q) := by
  apply impTrans'' (and₁' diaDuality);
  apply impTrans'' ?h (and₂' diaDuality);
  apply contra₀';
  apply axiomK';
  apply nec;
  apply contra₀';
  exact or₂;
@[simp] lemma dia_or_inst₂! : 𝓢 ⊢! ◇q ➝ ◇(p ⋎ q) := ⟨diaOrInst₂⟩

def collect_dia_or : 𝓢 ⊢ ◇p ⋎ ◇q ➝ ◇(p ⋎ q) := or₃'' diaOrInst₁ diaOrInst₂
@[simp] lemma collect_dia_or! : 𝓢 ⊢! ◇p ⋎ ◇q ➝ ◇(p ⋎ q) := ⟨collect_dia_or⟩

def collect_dia_or' (h : 𝓢 ⊢ ◇p ⋎ ◇q) : 𝓢 ⊢ ◇(p ⋎ q) := collect_dia_or ⨀ h
@[simp] lemma collect_dia_or'! (h : 𝓢 ⊢! ◇p ⋎ ◇q) : 𝓢 ⊢! ◇(p ⋎ q) := ⟨collect_dia_or' h.some⟩

-- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.
@[simp] lemma distribute_multidia_and!: 𝓢 ⊢! ◇^[n](p ⋏ q) ➝ ◇^[n]p ⋏ ◇^[n]q := by
  suffices h : 𝓢 ⊢! ∼(□^[n](∼(p ⋏ q))) ➝ ∼(□^[n](∼p)) ⋏ ∼(□^[n](∼q)) by
    exact imp_trans''! (imp_trans''! (and₁'! multidia_duality!) h) $ and_replace! (and₂'! multidia_duality!) (and₂'! multidia_duality!);
  apply FiniteContext.deduct'!;
  apply demorgan₃'!;
  apply FiniteContext.deductInv'!;
  apply contra₀'!;
  apply imp_trans''! collect_multibox_or! (imply_multibox_distribute'! demorgan₁!)

@[simp] lemma distribute_dia_and! : 𝓢 ⊢! ◇(p ⋏ q) ➝ ◇p ⋏ ◇q := distribute_multidia_and! (n := 1)

-- TODO: `iffConjMultidiaMultidiaconj` is computable but it's too slow, so leave it.
@[simp] lemma iff_conjmultidia_multidiaconj! : 𝓢 ⊢! ◇^[n](⋀Γ) ➝ ⋀(◇'^[n]Γ) := by
  induction Γ using List.induction_with_singleton with
  | hcons p Γ h ih =>
    simp_all;
    exact imp_trans''! distribute_multidia_and! $ by
      apply deduct'!;
      apply iff_provable_list_conj.mpr;
      intro q hq;
      simp at hq;
      cases hq with
      | inl => subst_vars; exact and₁'! id!;
      | inr hq =>
        obtain ⟨r, hr₁, hr₂⟩ := hq;
        exact (iff_provable_list_conj.mp $ (of'! ih) ⨀ (and₂'! $ id!)) q (by aesop);
  | _ => simp

-- def distributeDiaAnd' (h : 𝓢 ⊢ ◇(p ⋏ q)) : 𝓢 ⊢ ◇p ⋏ ◇q := distributeDiaAnd ⨀ h
lemma distribute_dia_and'! (h : 𝓢 ⊢! ◇(p ⋏ q)) : 𝓢 ⊢! ◇p ⋏ ◇q := distribute_dia_and! ⨀ h

def boxdotAxiomK : 𝓢 ⊢ ⊡(p ➝ q) ➝ (⊡p ➝ ⊡q) := by
  apply deduct';
  apply deduct;
  have d : [p ⋏ □p, (p ➝ q) ⋏ □(p ➝ q)] ⊢[𝓢] (p ➝ q) ⋏ □(p ➝ q) := FiniteContext.byAxm;
  exact and₃' ((and₁' d) ⨀ (and₁' (q := □p) (FiniteContext.byAxm))) <|
    (axiomK' $ and₂' d) ⨀ (and₂' (p := p) (FiniteContext.byAxm));
@[simp] lemma boxdot_axiomK! : 𝓢 ⊢! ⊡(p ➝ q) ➝ (⊡p ➝ ⊡q) := ⟨boxdotAxiomK⟩

def boxdotAxiomT : 𝓢 ⊢ ⊡p ➝ p := by exact and₁;
@[simp] lemma boxdot_axiomT! : 𝓢 ⊢! ⊡p ➝ p := ⟨boxdotAxiomT⟩

def boxdotNec (d : 𝓢 ⊢ p) : 𝓢 ⊢ ⊡p := and₃' d (nec d)
lemma boxdot_nec! (d : 𝓢 ⊢! p) : 𝓢 ⊢! ⊡p := ⟨boxdotNec d.some⟩

def boxdotBox : 𝓢 ⊢ ⊡p ➝ □p := by exact and₂;
lemma boxdot_box! : 𝓢 ⊢! ⊡p ➝ □p := ⟨boxdotBox⟩

def BoxBoxdot_BoxDotbox : 𝓢 ⊢ □⊡p ➝ ⊡□p := impTrans'' distribute_box_and (impId _)
lemma boxboxdot_boxdotbox : 𝓢 ⊢! □⊡p ➝ ⊡□p := ⟨BoxBoxdot_BoxDotbox⟩

end K


section KT

variable [System.KT 𝓢]

def diaTc : 𝓢 ⊢ p ➝ ◇p := by
  apply impTrans'' ?_ (and₂' diaDuality);
  exact impTrans'' dni $ contra₀' axiomT;
@[simp] lemma diaTc! : 𝓢 ⊢! p ➝ ◇p := ⟨diaTc⟩

def diaTc' [HasDiaDuality 𝓢] (h : 𝓢 ⊢ p) : 𝓢 ⊢ ◇p := diaTc ⨀ h
lemma diaTc'! [HasDiaDuality 𝓢] (h : 𝓢 ⊢! p) : 𝓢 ⊢! ◇p := ⟨diaTc' h.some⟩

end KT



section KD

variable [System.KD 𝓢]

private def P_of_D : 𝓢 ⊢ Axioms.P := by
  have : 𝓢 ⊢ ∼∼□(∼⊥) := dni' $ nec notbot;
  have : 𝓢 ⊢ ∼◇⊥ := (contra₀' $ and₁' diaDuality) ⨀ this;
  exact (contra₀' axiomD) ⨀ this;
instance : HasAxiomP 𝓢 := ⟨P_of_D⟩
instance : System.KP 𝓢 where

end KD


section KP

variable [System.KP 𝓢]

private def D_of_P [HasDiaDuality 𝓢] : 𝓢 ⊢ Axioms.D p := by
  have : 𝓢 ⊢ p ➝ (∼p ➝ ⊥) := impTrans'' dni (and₁' neg_equiv);
  have : 𝓢 ⊢ □p ➝ □(∼p ➝ ⊥) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □p ➝ (□(∼p) ➝ □⊥) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □p ➝ (∼□⊥ ➝ ∼□(∼p)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □p ➝ ∼□(∼p) := impSwap' this ⨀ axiomP;
  exact impTrans'' this (and₂' diaDuality);
instance : HasAxiomD 𝓢 := ⟨fun _ ↦ D_of_P⟩
instance : System.KD 𝓢 where

end KP


section K4

variable [System.K4 𝓢]

def imply_BoxBoxdot_Box: 𝓢 ⊢  □⊡p ➝ □p := by
  exact impTrans'' distribute_box_and and₁
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢! □⊡p ➝ □p := ⟨imply_BoxBoxdot_Box⟩

def imply_Box_BoxBoxdot : 𝓢 ⊢ □p ➝ □⊡p := by
  exact impTrans'' (implyRightAnd (impId _) axiomFour) collect_box_and
@[simp] lemma imply_box_boxboxdot! : 𝓢 ⊢! □p ➝ □⊡p := ⟨imply_Box_BoxBoxdot⟩

def imply_Box_BoxBoxdot' (h : 𝓢 ⊢ □p) : 𝓢 ⊢ □⊡p := imply_Box_BoxBoxdot ⨀ h
def imply_Box_BoxBoxdot'! (h : 𝓢 ⊢! □p) : 𝓢 ⊢! □⊡p := ⟨imply_Box_BoxBoxdot' h.some⟩

def iff_Box_BoxBoxdot : 𝓢 ⊢ □p ⭤ □⊡p := by
  apply iffIntro;
  . exact imply_Box_BoxBoxdot
  . exact imply_BoxBoxdot_Box;
@[simp] lemma iff_box_boxboxdot! : 𝓢 ⊢! □p ⭤ □⊡p := ⟨iff_Box_BoxBoxdot⟩

def iff_Box_BoxdotBox : 𝓢 ⊢ □p ⭤ ⊡□p := by
  apply iffIntro;
  . exact impTrans'' (implyRightAnd (impId _) axiomFour) (impId _)
  . exact and₁
@[simp] lemma iff_box_boxdotbox! : 𝓢 ⊢! □p ⭤ ⊡□p := ⟨iff_Box_BoxdotBox⟩

def iff_Boxdot_BoxdotBoxdot : 𝓢 ⊢ ⊡p ⭤ ⊡⊡p := by
  apply iffIntro;
  . exact implyRightAnd (impId _) (impTrans'' boxdotBox (and₁' iff_Box_BoxBoxdot));
  . exact and₁;
@[simp] lemma iff_boxdot_boxdotboxdot : 𝓢 ⊢! ⊡p ⭤ ⊡⊡p := ⟨iff_Boxdot_BoxdotBoxdot⟩

def boxdotAxiomFour : 𝓢 ⊢ ⊡p ➝ ⊡⊡p := and₁' iff_Boxdot_BoxdotBoxdot
@[simp] lemma boxdot_axiomFour! : 𝓢 ⊢! ⊡p ➝ ⊡⊡p := ⟨boxdotAxiomFour⟩

end K4


section K4Loeb

variable [System.K4Loeb 𝓢]

private def axiomL_of_K4Loeb : 𝓢 ⊢ Axioms.L p := by
  dsimp [Axioms.L];
  generalize e : □(□p ➝ p) ➝ □p = q;
  have d₁ : [□(□p ➝ p), □q] ⊢[𝓢] □□(□p ➝ p) ➝ □□p := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₂ : [□(□p ➝ p), □q] ⊢[𝓢] □□p ➝ □p := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₃ : 𝓢 ⊢ □(□p ➝ p) ➝ □□(□p ➝ p) := axiomFour;
  have : 𝓢 ⊢ □q ➝ q := by
    nth_rw 2 [←e]; apply deduct'; apply deduct;
    exact d₂ ⨀ (d₁ ⨀ ((of d₃) ⨀ (FiniteContext.byAxm)));
  exact loeb this;
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ axiomL_of_K4Loeb⟩
instance : System.GL 𝓢 where

end K4Loeb


section K4Henkin

variable [System.K4Henkin 𝓢]

instance : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ iffIntro (axiomK' $ nec h) axiomFour);
instance : System.K4Loeb 𝓢 where

end K4Henkin


section K4H

variable [System.K4H 𝓢]

instance : HenkinRule 𝓢 where
  henkin h := (and₁' h) ⨀ (axiomH ⨀ nec h);
instance : System.K4Henkin 𝓢 where

end K4H


section S4

variable [System.S4 𝓢]

def iff_box_boxdot : 𝓢 ⊢ □p ⭤ ⊡p := by
  apply iffIntro;
  . exact implyRightAnd (axiomT) (impId _);
  . exact and₂;
@[simp] lemma iff_box_boxdot! : 𝓢 ⊢! □p ⭤ ⊡p := ⟨iff_box_boxdot⟩

def iff_dia_diadot : 𝓢 ⊢ ◇p ⭤ ⟐p := by
  apply iffIntro;
  . exact or₂;
  . exact or₃'' diaTc (impId _)
@[simp] lemma iff_dia_diadot! : 𝓢 ⊢! ◇p ⭤ ⟐p := ⟨iff_dia_diadot⟩

end S4




section KTc

variable [System.KTc 𝓢]

private def axiomFour_of_Tc : 𝓢 ⊢ Axioms.Four p := axiomTc
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ axiomFour_of_Tc⟩

def diaT : 𝓢 ⊢ ◇p ➝ p := by
  apply impTrans'' (and₁' diaDuality) ?_;
  apply contra₂';
  exact axiomTc;
@[simp] lemma diaT! : 𝓢 ⊢! ◇p ➝ p := ⟨diaT⟩

def diaT' (h : 𝓢 ⊢ ◇p) : 𝓢 ⊢ p := diaT ⨀ h
lemma diaT'! (h : 𝓢 ⊢! ◇p) : 𝓢 ⊢! p := ⟨diaT' h.some⟩

private def axiomFive_of_Tc : 𝓢 ⊢ ◇p ➝ □◇p := axiomTc
instance : HasAxiomFive 𝓢 := ⟨fun _ ↦ axiomFive_of_Tc⟩

end KTc


section Triv

variable [System.Triv 𝓢]

private def axiomGrz_of_Tc_and_T : 𝓢 ⊢ □(□(p ➝ □p) ➝ p) ➝ p := by
  have : 𝓢 ⊢ p ➝ □p := axiomTc;
  have d₁ := nec this;
  have d₂ : 𝓢 ⊢ □(p ➝ □p) ➝ ((□(p ➝ □p)) ➝ p) ➝ p := p_pq_q;
  have := d₂ ⨀ d₁;
  exact impTrans'' axiomT this;

instance : HasAxiomGrz 𝓢 := ⟨fun _ ↦ axiomGrz_of_Tc_and_T⟩

end Triv


section Ver

variable [System.Ver 𝓢]

private def axiomTc_of_Ver : 𝓢 ⊢ Axioms.Tc p := dhyp _ axiomVer
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ axiomTc_of_Ver⟩

private def axiomL_of_Ver : 𝓢 ⊢ Axioms.L p := dhyp _ axiomVer
instance : HasAxiomL 𝓢 := ⟨fun _ ↦ axiomL_of_Ver⟩

def bot_of_dia : 𝓢 ⊢ ◇p ➝ ⊥ := by
  have : 𝓢 ⊢ ∼◇p ➝ (◇p ➝ ⊥) := and₁' $ neg_equiv (𝓢 := 𝓢) (p := ◇p);
  exact this ⨀ (contra₀' (and₁' diaDuality) ⨀ by
    apply dni';
    apply axiomVer;
  );
lemma bot_of_dia! : 𝓢 ⊢! ◇p ➝ ⊥ := ⟨bot_of_dia⟩

def bot_of_dia' (h : 𝓢 ⊢ ◇p) : 𝓢 ⊢ ⊥ := bot_of_dia ⨀ h
lemma bot_of_dia'! (h : 𝓢 ⊢! ◇p) : 𝓢 ⊢! ⊥ := ⟨bot_of_dia' h.some⟩

end Ver


section GL

variable [System.GL 𝓢]

private def axiomFour_of_L : 𝓢 ⊢ Axioms.Four p := by
  dsimp [Axioms.Four];
  have : 𝓢 ⊢ p ➝ (⊡□p ➝ ⊡p) := by
    apply deduct';
    apply deduct;
    exact and₃' (FiniteContext.byAxm) (and₁' (q := □□p) $ FiniteContext.byAxm);
  have : 𝓢 ⊢ p ➝ (□⊡p ➝ ⊡p) := impTrans'' this (implyLeftReplace BoxBoxdot_BoxDotbox);
  exact impTrans'' (impTrans'' (implyBoxDistribute' this) axiomL) (implyBoxDistribute' $ and₂);
instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ axiomFour_of_L⟩
instance : System.K4 𝓢 where

def goedel2 : 𝓢 ⊢ (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := by
  apply negReplaceIff';
  apply iffIntro;
  . apply implyBoxDistribute';
    exact efq;
  . exact impTrans'' (by
      apply implyBoxDistribute';
      exact and₁' neg_equiv;
    ) axiomL;
lemma goedel2! : 𝓢 ⊢! (∼(□⊥) ⭤ ∼(□(∼(□⊥))) : F) := ⟨goedel2⟩

def goedel2'.mp : 𝓢 ⊢ (∼(□⊥) : F) → 𝓢 ⊢ ∼(□(∼(□⊥)) : F) := by intro h; exact (and₁' goedel2) ⨀ h;
def goedel2'.mpr : 𝓢 ⊢ ∼(□(∼(□⊥)) : F) → 𝓢 ⊢ (∼(□⊥) : F) := by intro h; exact (and₂' goedel2) ⨀ h;
lemma goedel2'! : 𝓢 ⊢! (∼(□⊥) : F) ↔ 𝓢 ⊢! ∼(□(∼(□⊥)) : F) := ⟨λ ⟨h⟩ ↦ ⟨goedel2'.mp h⟩, λ ⟨h⟩ ↦ ⟨goedel2'.mpr h⟩⟩

private def axiomH_of_GL : 𝓢 ⊢ Axioms.H p := impTrans'' (implyBoxDistribute' and₁) axiomL
instance : HasAxiomH 𝓢 := ⟨fun _ ↦ axiomH_of_GL⟩

private noncomputable def boxdot_Grz_of_L1 : 𝓢 ⊢ (⊡(⊡(p ➝ ⊡p) ➝ p)) ➝ (□(p ➝ ⊡p) ➝ p) := by
  have : 𝓢 ⊢ (□(p ➝ ⊡p) ⋏ ∼p) ➝ ⊡(p ➝ ⊡p) := by
    apply deduct';
    apply and₃';
    . exact (of efq_imply_not₁) ⨀ and₂;
    . exact (of (impId _)) ⨀ and₁;
  have : 𝓢 ⊢ ∼⊡(p ➝ ⊡p) ➝ (∼□(p ➝ ⊡p) ⋎ p) := impTrans'' (contra₀' this) $ impTrans'' demorgan₄ (orReplaceRight dne);
  have : 𝓢 ⊢ (∼⊡(p ➝ ⊡p) ⋎ p) ➝ (∼□(p ➝ ⊡p) ⋎ p) := or₃'' this or₂;
  have : 𝓢 ⊢ ∼⊡(p ➝ ⊡p) ⋎ p ➝ □(p ➝ ⊡p) ➝ p := impTrans'' this implyOfNotOr;
  have : 𝓢 ⊢ (⊡(p ➝ ⊡p) ➝ p) ➝ (□(p ➝ ⊡p) ➝ p) := impTrans'' NotOrOfImply this;
  exact impTrans'' boxdotAxiomT this;

noncomputable def boxdot_Grz_of_L : 𝓢 ⊢ ⊡(⊡(p ➝ ⊡p) ➝ p) ➝ p := by
  have : 𝓢 ⊢ □(⊡(p ➝ ⊡p) ➝ p) ➝ □⊡(p ➝ ⊡p) ➝ □p := axiomK;
  have : 𝓢 ⊢ □(⊡(p ➝ ⊡p) ➝ p) ➝ □(p ➝ ⊡p) ➝ □p := impTrans'' this $ implyLeftReplace $ imply_Box_BoxBoxdot;
  have : 𝓢 ⊢ □(⊡(p ➝ ⊡p) ➝ p) ➝ □(p ➝ ⊡p) ➝ (p ➝ ⊡p) := by
    apply deduct'; apply deduct; apply deduct;
    exact and₃' FiniteContext.byAxm $ (of this) ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have : 𝓢 ⊢ □□(⊡(p ➝ ⊡p) ➝ p) ➝ □(□(p ➝ ⊡p) ➝ (p ➝ ⊡p)) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(⊡(p ➝ ⊡p) ➝ p) ➝ □(□(p ➝ ⊡p) ➝ (p ➝ ⊡p)) := impTrans'' axiomFour this;
  have : 𝓢 ⊢ □(⊡(p ➝ ⊡p) ➝ p) ➝ □(p ➝ ⊡p) := impTrans'' this axiomL;
  have : 𝓢 ⊢ ⊡(⊡(p ➝ ⊡p) ➝ p) ➝ □(p ➝ ⊡p) := impTrans'' boxdotBox this;
  exact mdp₁ boxdot_Grz_of_L1 this;
@[simp] lemma boxdot_Grz_of_L! : 𝓢 ⊢! ⊡(⊡(p ➝ ⊡p) ➝ p) ➝ p := ⟨boxdot_Grz_of_L⟩

def imply_boxdot_boxdot_of_imply_boxdot_plain (h : 𝓢 ⊢ ⊡p ➝ q) : 𝓢 ⊢ ⊡p ➝ ⊡q := by
  have : 𝓢 ⊢ □⊡p ➝ □q := implyBoxDistribute' h;
  have : 𝓢 ⊢ □p ➝ □q := impTrans'' imply_Box_BoxBoxdot this;
  have : 𝓢 ⊢ ⊡p ➝ □q := impTrans'' boxdotBox this;
  exact implyRightAnd h this;
lemma imply_boxdot_boxdot_of_imply_boxdot_plain! (h : 𝓢 ⊢! ⊡p ➝ q) : 𝓢 ⊢! ⊡p ➝ ⊡q := ⟨imply_boxdot_boxdot_of_imply_boxdot_plain h.some⟩

def imply_boxdot_axiomT_of_imply_boxdot_boxdot (h : 𝓢 ⊢ ⊡p ➝ ⊡q) : 𝓢 ⊢ ⊡p ➝ (□q ➝ q) := by
  apply deduct';
  apply deduct;
  have : [□q, ⊡p] ⊢[𝓢] ⊡q := (FiniteContext.of h) ⨀ (FiniteContext.byAxm);
  exact and₁' this;
lemma imply_boxdot_axiomT_of_imply_boxdot_boxdot! (h : 𝓢 ⊢! ⊡p ➝ ⊡q) : 𝓢 ⊢! ⊡p ➝ (□q ➝ q) := ⟨imply_boxdot_axiomT_of_imply_boxdot_boxdot h.some⟩

def imply_box_box_of_imply_boxdot_axiomT (h : 𝓢 ⊢ ⊡p ➝ (□q ➝ q)) : 𝓢 ⊢ □p ➝ □q := by
  have : 𝓢 ⊢ □⊡p ➝ □(□q ➝ q) := implyBoxDistribute' h;
  have : 𝓢 ⊢ □⊡p ➝ □q := impTrans'' this axiomL;
  exact impTrans'' imply_Box_BoxBoxdot this;
lemma imply_box_box_of_imply_boxdot_axiomT! (h : 𝓢 ⊢! ⊡p ➝ (□q ➝ q)) : 𝓢 ⊢! □p ➝ □q := ⟨imply_box_box_of_imply_boxdot_axiomT h.some⟩

lemma imply_box_box_of_imply_boxdot_plain! (h : 𝓢 ⊢! ⊡p ➝ q) : 𝓢 ⊢! □p ➝ □q := by
  exact imply_box_box_of_imply_boxdot_axiomT! $ imply_boxdot_axiomT_of_imply_boxdot_boxdot! $ imply_boxdot_boxdot_of_imply_boxdot_plain! h

end GL


section Grz

variable [System.Grz 𝓢]

noncomputable def lemma_Grz₁ : 𝓢 ⊢ □p ➝ □(□((p ⋏ (□p ➝ □□p)) ➝ □(p ⋏ (□p ➝ □□p))) ➝ (p ⋏ (□p ➝ □□p))) := by
  let q := p ⋏ (□p ➝ □□p);
  have    : 𝓢 ⊢ ((□p ➝ □□p) ➝ □p) ➝ □p := peirce
  have    : 𝓢 ⊢ (p ➝ ((□p ➝ □□p) ➝ □p)) ➝ (p ➝ □p) := dhyp_imp' this;
  have d₁ : 𝓢 ⊢ (q ➝ □p) ➝ p ➝ □p := impTrans'' (and₁' $ andImplyIffImplyImply p (□p ➝ □□p) (□p)) this;
  have    : 𝓢 ⊢ q ➝ p := and₁;
  have    : 𝓢 ⊢ □q ➝ □p := implyBoxDistribute' this;
  have d₂ : 𝓢 ⊢ (q ➝ □q) ➝ (q ➝ □p) := dhyp_imp' this;
  have    : 𝓢 ⊢ (q ➝ □q) ➝ p ➝ □p := impTrans'' d₂ d₁;
  have    : 𝓢 ⊢ □(q ➝ □q) ➝ □(p ➝ □p) := implyBoxDistribute' this;
  have    : 𝓢 ⊢ □(q ➝ □q) ➝ (□p ➝ □□p) := impTrans'' this axiomK;
  have    : 𝓢 ⊢ (p ➝ □(q ➝ □q)) ➝ (p ➝ (□p ➝ □□p)) := dhyp_imp' this;
  have    : 𝓢 ⊢ p ➝ (□(q ➝ □q) ➝ (p ⋏ (□p ➝ □□p))) := by
    apply deduct';
    apply deduct;
    apply and₃';
    . exact FiniteContext.byAxm;
    . exact (of this) ⨀ (dhyp p FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have    : 𝓢 ⊢ p ➝ (□(q ➝ □q) ➝ q) := this;
  exact implyBoxDistribute' this;
lemma lemma_Grz₁! : 𝓢 ⊢! (□p ➝ □(□((p ⋏ (□p ➝ □□p)) ➝ □(p ⋏ (□p ➝ □□p))) ➝ (p ⋏ (□p ➝ □□p)))) := ⟨lemma_Grz₁⟩

noncomputable def lemma_Grz₂ : 𝓢 ⊢ □p ➝ (p ⋏ (□p ➝ □□p)) := impTrans'' (lemma_Grz₁ (p := p)) axiomGrz

private noncomputable def Four_of_Grz : 𝓢 ⊢ □p ➝ □□p := ppq $ impTrans'' lemma_Grz₂ and₂
noncomputable instance : HasAxiomFour 𝓢 := ⟨fun _ ↦ Four_of_Grz⟩

private noncomputable def T_of_Grz : 𝓢 ⊢ □p ➝ p := impTrans'' lemma_Grz₂ and₁
noncomputable instance : HasAxiomT 𝓢 := ⟨fun _ ↦ T_of_Grz⟩

noncomputable instance : System.S4 𝓢 where

end Grz


section S5

variable [System.S5 𝓢]

-- MEMO: need more simple proof
def diabox_box : 𝓢 ⊢ ◇□p ➝ □p := by
  have : 𝓢 ⊢ ◇(∼p) ➝ □◇(∼p) := axiomFive;
  have : 𝓢 ⊢ ∼□◇(∼p) ➝ ∼◇(∼p) := contra₀' this;
  have : 𝓢 ⊢ ∼□◇(∼p) ➝ □p := impTrans'' this boxDuality_mpr;
  refine impTrans'' ?_ this;
  refine impTrans'' diaDuality_mp $ ?_
  apply contra₀';
  apply implyBoxDistribute';
  refine impTrans'' diaDuality_mp ?_;
  apply contra₀';
  apply implyBoxDistribute';
  apply dni;
@[simp] lemma diabox_box! : 𝓢 ⊢! ◇□p ➝ □p := ⟨diabox_box⟩

def diabox_box' (h : 𝓢 ⊢ ◇□p) : 𝓢 ⊢ □p := diabox_box ⨀ h
lemma diabox_box'! (h : 𝓢 ⊢! ◇□p) : 𝓢 ⊢! □p := ⟨diabox_box' h.some⟩


def rm_diabox : 𝓢 ⊢ ◇□p ➝ p := impTrans'' diabox_box axiomT
@[simp] lemma rm_diabox! : 𝓢 ⊢! ◇□p ➝ p := ⟨rm_diabox⟩

def rm_diabox' (h : 𝓢 ⊢ ◇□p) : 𝓢 ⊢ p := rm_diabox ⨀ h
lemma rm_diabox'! (h : 𝓢 ⊢! ◇□p) : 𝓢 ⊢! p := ⟨rm_diabox' h.some⟩

private def lem₁_diaT_of_S5Grz : 𝓢 ⊢ (∼□(∼p) ➝ ∼□(∼□p)) ➝ (◇p ➝ ◇□p) := impTrans'' (rev_dhyp_imp' diaDuality_mp) (dhyp_imp' diaDuality_mpr)

private def lem₂_diaT_of_S5Grz : 𝓢 ⊢ (◇p ➝ ◇□p) ➝ (◇p ➝ p) := dhyp_imp' rm_diabox

end S5


section S5Grz

variable [System.S5Grz 𝓢]

private def diaT_of_S5Grz : 𝓢 ⊢ ◇p ➝ p := by
  have : 𝓢 ⊢ (p ➝ □p) ➝ (∼□p ➝ ∼p) := contra₀;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ □(∼□p ➝ ∼p) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ (□(∼□p) ➝ □(∼p)) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ (∼□(∼p) ➝ ∼□(∼□p)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ (◇p ➝ ◇□p) := impTrans'' this lem₁_diaT_of_S5Grz;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ (◇p ➝ □p) := impTrans'' this $ dhyp_imp' diabox_box;
  have : 𝓢 ⊢ □(p ➝ □p) ➝ (◇p ➝ p) := impTrans'' this $ dhyp_imp' axiomT;
  have : 𝓢 ⊢ ◇p ➝ □(p ➝ □p) ➝ p := impSwap' this;
  have : 𝓢 ⊢ □◇p ➝ □(□(p ➝ □p) ➝ p) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □◇p ➝ p := impTrans'' this axiomGrz;
  exact impTrans'' axiomFive this;

private def Tc_of_S5Grz : 𝓢 ⊢ p ➝ □p := impTrans'' (contra₃' (impTrans'' (and₂' diaDuality) diaT_of_S5Grz)) box_dne
instance : HasAxiomTc 𝓢 := ⟨fun _ ↦ Tc_of_S5Grz⟩

end S5Grz


lemma contextual_nec! [System.K 𝓢] (h : Γ ⊢[𝓢]! p) : (□'Γ) ⊢[𝓢]! □p :=
  provable_iff.mpr $ imp_trans''! collect_box_conj! $ imply_box_distribute'! $ provable_iff.mp h

end


section Contextual

variable {F : Type*}  [LogicalConnective F] [Box F]
variable {S : Type*} [System F S] [DecidableEq F]
         {𝓢 : S} [System.Minimal 𝓢]
         {X : Set F} {p : F}


lemma Context.provable_iff_boxed : (□''X) *⊢[𝓢]! p ↔ ∃ Δ : List F, (∀ q ∈ □'Δ, q ∈ □''X) ∧ (□'Δ) ⊢[𝓢]! p := by
  constructor;
  . intro h;
    obtain ⟨Γ,sΓ, hΓ⟩ := Context.provable_iff.mp h;
    use □'⁻¹Γ;
    constructor;
    . rintro q hq;
      apply sΓ q;
      simp at hq;
      obtain ⟨r, _, rfl⟩ := hq;
      assumption;
    . apply FiniteContext.provable_iff.mpr;
      apply imp_trans''! ?_ (FiniteContext.provable_iff.mp hΓ);
      apply conjconj_subset!;
      intro q hq;
      have := sΓ q hq;
      obtain ⟨r, _, rfl⟩ := this;
      simp_all;
  . rintro ⟨Δ, hΔ, h⟩;
    apply Context.provable_iff.mpr;
    use □'Δ;

end Contextual

end LO.System

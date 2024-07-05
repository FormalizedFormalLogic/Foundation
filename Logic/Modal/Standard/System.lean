import Logic.Logic.HilbertStyle.Supplemental
import Logic.Modal.Standard.Axioms

namespace LO.System

section Systems

variable {S F : Type*} [LogicalConnective F] [StandardModalLogicalConnective F] [System F S]
variable (𝓢 : S)

class Necessitation where
  nec {p : F} : 𝓢 ⊢ p → 𝓢 ⊢ □p

class LoebRule where
  loeb {p : F} : 𝓢 ⊢ □p ⟶ p → 𝓢 ⊢ p

class HenkinRule where
  henkin {p : F} : 𝓢 ⊢ □p ⟷ p → 𝓢 ⊢ p

class HasAxiomK where
  K (p q : F) : 𝓢 ⊢ Axioms.K p q

class HasAxiomT where
  T (p : F) : 𝓢 ⊢ Axioms.T p

class HasAxiomD where
  D (p : F) : 𝓢 ⊢ Axioms.D p

class HasAxiomB where
  B (p : F) : 𝓢 ⊢ Axioms.B p

class HasAxiomFour where
  Four (p : F) : 𝓢 ⊢ Axioms.Four p

class HasAxiomFive where
  Five (p : F) : 𝓢 ⊢ Axioms.Five p

class HasAxiomL where
  L (p : F) : 𝓢 ⊢ Axioms.L p

class HasAxiomDot2 where
  Dot2 (p : F) : 𝓢 ⊢ Axioms.Dot2 p

class HasAxiomDot3 where
  Dot3 (p q : F) : 𝓢 ⊢ Axioms.Dot3 p q

class HasAxiomGrz where
  Grz (p : F) : 𝓢 ⊢ Axioms.Grz p

class HasAxiomTc where
  Tc (p : F) : 𝓢 ⊢ Axioms.Tc p

class HasAxiomVer where
  Ver (p : F) : 𝓢 ⊢ Axioms.Ver p

class HasAxiomH where
  H (p : F) : 𝓢 ⊢ Axioms.H p

protected class K extends System.Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢

protected class KT extends System.K 𝓢, HasAxiomT 𝓢

protected class KD extends System.K 𝓢, HasAxiomD 𝓢

protected class K4 extends System.K 𝓢, HasAxiomFour 𝓢

protected class S4 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢

protected class S5 extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢

protected class S4Dot2 extends System.S4 𝓢, HasAxiomDot2 𝓢

protected class S4Dot3 extends System.S4 𝓢, HasAxiomDot3 𝓢

protected class S4Grz extends System.S4 𝓢, HasAxiomGrz 𝓢

protected class GL extends System.K 𝓢, HasAxiomL 𝓢

protected class Triv extends System.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢

protected class Ver extends System.K 𝓢, HasAxiomVer 𝓢

protected class K4H extends System.K4 𝓢, HasAxiomH 𝓢

protected class K4Loeb extends System.K4 𝓢, LoebRule 𝓢

protected class K4Henkin extends System.K4 𝓢, HenkinRule 𝓢

end Systems

section


variable {F : Type*} [StandardModalLogicalConnective F][DecidableEq F]
variable {S : Type*} [System F S]
variable {p q r : F} {Γ Δ : List F}

variable {𝓢 : S}
variable [System.Classical 𝓢] [System.NegationEquiv 𝓢]

open FiniteContext
open Necessitation

variable [Necessitation 𝓢]

alias nec := Necessitation.nec

lemma nec! : 𝓢 ⊢! p → 𝓢 ⊢! □p := by rintro ⟨hp⟩; exact ⟨nec hp⟩

def multinec : 𝓢 ⊢ p → 𝓢 ⊢ □^[n]p := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;
lemma multinec! : 𝓢 ⊢! p → 𝓢 ⊢! □^[n]p := by rintro ⟨hp⟩; exact ⟨multinec hp⟩


variable [HasAxiomK 𝓢]

def axiomK [HasAxiomK 𝓢] : 𝓢 ⊢ □(p ⟶ q) ⟶ □p ⟶ □q := HasAxiomK.K _ _
@[simp] lemma axiomK! [HasAxiomK 𝓢] : 𝓢 ⊢! □(p ⟶ q) ⟶ □p ⟶ □q := ⟨axiomK⟩

instance [HasAxiomK 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ FiniteContext.of axiomK⟩
instance [HasAxiomK 𝓢] (Γ : Context F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ Context.of axiomK⟩

variable [HasAxiomK 𝓢]

def axiomK' (h : 𝓢 ⊢ □(p ⟶ q)) : 𝓢 ⊢ □p ⟶ □q := axiomK ⨀ h
@[simp] lemma axiomK'! (h : 𝓢 ⊢! □(p ⟶ q)) : 𝓢 ⊢! □p ⟶ □q := ⟨axiomK' h.some⟩

def axiomK'' (h₁ : 𝓢 ⊢ □(p ⟶ q)) (h₂ : 𝓢 ⊢ □p) : 𝓢 ⊢ □q := axiomK' h₁ ⨀ h₂
@[simp] lemma axiomK''! (h₁ : 𝓢 ⊢! □(p ⟶ q)) (h₂ : 𝓢 ⊢! □p) : 𝓢 ⊢! □q := ⟨axiomK'' h₁.some h₂.some⟩

def multibox_axiomK : 𝓢 ⊢ □^[n](p ⟶ q) ⟶ □^[n]p ⟶ □^[n]q := by
  induction n with
  | zero => simp; apply impId;
  | succ n ih => simpa using impTrans'' (axiomK' $ nec ih) (by apply axiomK);

@[simp] lemma multibox_axiomK! : 𝓢 ⊢! □^[n](p ⟶ q) ⟶ □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK⟩

def multibox_axiomK' (h : 𝓢 ⊢ □^[n](p ⟶ q)) : 𝓢 ⊢ □^[n]p ⟶ □^[n]q := multibox_axiomK ⨀ h
@[simp] lemma multibox_axiomK'! (h : 𝓢 ⊢! □^[n](p ⟶ q)) : 𝓢 ⊢! □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK' h.some⟩

alias multiboxedImplyDistribute := multibox_axiomK'
alias multiboxed_imply_distribute! := multibox_axiomK'!


def boxIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (□p ⟷ □q) := by
  apply iffIntro;
  . exact axiomK' $ nec $ and₁' h;
  . exact axiomK' $ nec $ and₂' h;
@[simp] lemma box_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □p ⟷ □q := ⟨boxIff' h.some⟩

def multiboxIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ □^[n]p ⟷ □^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
@[simp] lemma multibox_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □^[n]p ⟷ □^[n]q := ⟨multiboxIff' h.some⟩


def diaIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (◇p ⟷ ◇q) := by
  simp only [StandardModalLogicalConnective.duality'];
  apply negReplaceIff';
  apply boxIff';
  apply negReplaceIff';
  assumption
@[simp] lemma dia_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ◇p ⟷ ◇q := ⟨diaIff' h.some⟩

def multidiaIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ ◇^[n]p ⟷ ◇^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
@[simp] lemma multidia_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! ◇^[n]p ⟷ ◇^[n]q := ⟨multidiaIff' h.some⟩


def multiboxDuality : 𝓢 ⊢ □^[n]p ⟷ ~(◇^[n](~p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp [StandardModalLogicalConnective.duality'];
    exact iffTrans'' (boxIff' ih) dn
@[simp] lemma multibox_duality! : 𝓢 ⊢! □^[n]p ⟷ ~(◇^[n](~p)) := ⟨multiboxDuality⟩

def boxDuality : 𝓢 ⊢ □p ⟷ ~(◇~p) := multiboxDuality (n := 1)
@[simp] lemma box_duality! : 𝓢 ⊢! □p ⟷ ~(◇~p) := ⟨boxDuality⟩

lemma multibox_duality'! : 𝓢 ⊢! □^[n]p ↔ 𝓢 ⊢! ~(◇^[n](~p)) := by
  constructor;
  . intro h; exact (and₁'! multibox_duality!) ⨀ h;
  . intro h; exact (and₂'! multibox_duality!) ⨀ h;

lemma box_duality'! : 𝓢 ⊢! □p ↔ 𝓢 ⊢! ~(◇~p) := multibox_duality'! (n := 1)


def multidiaDuality : 𝓢 ⊢ ◇^[n]p ⟷ ~(□^[n](~p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp [StandardModalLogicalConnective.duality'];
    apply negReplaceIff';
    apply boxIff';
    exact iffTrans'' (negReplaceIff' ih) (iffComm' dn)
@[simp] lemma multidia_duality! : 𝓢 ⊢! ◇^[n]p ⟷ ~(□^[n](~p)) := ⟨multidiaDuality⟩

def diaDuality : 𝓢 ⊢ ◇p ⟷ ~(□~p) := multidiaDuality (n := 1)
@[simp] lemma diaDuality! : 𝓢 ⊢! ◇p ⟷ ~(□~p) := ⟨diaDuality⟩

lemma multidia_duality'! : 𝓢 ⊢! ◇^[n]p ↔ 𝓢 ⊢! ~(□^[n](~p)) := by
  constructor;
  . intro h; exact (and₁'! multidia_duality!) ⨀ h;
  . intro h; exact (and₂'! multidia_duality!) ⨀ h;
lemma dia_duality'! : 𝓢 ⊢! ◇p ↔ 𝓢 ⊢! ~(□~p) := multidia_duality'! (n := 1)


def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
@[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := ⟨multiboxverum⟩

def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
@[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := ⟨boxverum⟩


def implyMultiboxDistribute' (h : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ □^[n]p ⟶ □^[n]q := multibox_axiomK' $ multinec h
lemma imply_multibox_distribute'! (h : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! □^[n]p ⟶ □^[n]q := ⟨implyMultiboxDistribute' h.some⟩

def implyBoxDistribute' (h : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ □p ⟶ □q := implyMultiboxDistribute' (n := 1) h
lemma imply_box_distribute'! (h : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! □p ⟶ □q := ⟨implyBoxDistribute' h.some⟩


def distribute_multibox_and : 𝓢 ⊢ □^[n](p ⋏ q) ⟶ □^[n]p ⋏ □^[n]q := implyRightAnd (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)
@[simp] lemma distribute_multibox_and! : 𝓢 ⊢! □^[n](p ⋏ q) ⟶ □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and⟩

def distribute_box_and : 𝓢 ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := distribute_multibox_and (n := 1)
@[simp] lemma distribute_box_and! : 𝓢 ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_and⟩

def distribute_multibox_and' (h : 𝓢 ⊢ □^[n](p ⋏ q)) : 𝓢 ⊢ □^[n]p ⋏ □^[n]q := distribute_multibox_and ⨀ h
lemma distribute_multibox_and'! (d : 𝓢 ⊢! □^[n](p ⋏ q)) : 𝓢 ⊢! □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and' d.some⟩

def distribute_box_and' (h : 𝓢 ⊢ □(p ⋏ q)) : 𝓢 ⊢ □p ⋏ □q := distribute_multibox_and' (n := 1) h
lemma distribute_box_and'! (d : 𝓢 ⊢! □(p ⋏ q)) : 𝓢 ⊢! □p ⋏ □q := ⟨distribute_box_and' d.some⟩


def collect_multibox_and : 𝓢 ⊢ □^[n]p ⋏ □^[n]q ⟶ □^[n](p ⋏ q) := by
  have d₁ : 𝓢 ⊢ □^[n]p ⟶ □^[n](q ⟶ p ⋏ q) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](q ⟶ p ⋏ q) ⟶ (□^[n]q ⟶ □^[n](p ⋏ q)) := multibox_axiomK;
  exact (and₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans'' d₁ d₂);
@[simp] lemma collect_multibox_and! : 𝓢 ⊢! □^[n]p ⋏ □^[n]q ⟶ □^[n](p ⋏ q) := ⟨collect_multibox_and⟩

def collect_box_and : 𝓢 ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := collect_multibox_and (n := 1)
@[simp] lemma collect_box_and! : 𝓢 ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_and⟩

def collect_multibox_and' (h : 𝓢 ⊢ □^[n]p ⋏ □^[n]q) : 𝓢 ⊢ □^[n](p ⋏ q) := collect_multibox_and ⨀ h
lemma collect_multibox_and'! (h : 𝓢 ⊢! □^[n]p ⋏ □^[n]q) : 𝓢 ⊢! □^[n](p ⋏ q) := ⟨collect_multibox_and' h.some⟩

def collect_box_and' (h : 𝓢 ⊢ □p ⋏ □q) : 𝓢 ⊢ □(p ⋏ q) := collect_multibox_and' (n := 1) h
lemma collect_box_and'! (h : 𝓢 ⊢! □p ⋏ □q) : 𝓢 ⊢! □(p ⋏ q) := ⟨collect_box_and' h.some⟩


lemma multiboxConj'_iff! : 𝓢 ⊢! □^[n]⋀Γ ↔ ∀ p ∈ Γ, 𝓢 ⊢! □^[n]p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
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
lemma boxConj'_iff! : 𝓢 ⊢! □⋀Γ ↔ ∀ p ∈ Γ, 𝓢 ⊢! □p := multiboxConj'_iff! (n := 1)

lemma multiboxconj'_of_conj'multibox! (d : 𝓢 ⊢! ⋀□'^[n]Γ) : 𝓢 ⊢! □^[n]⋀Γ := by
  apply multiboxConj'_iff!.mpr;
  intro p hp;
  exact iff_provable_list_conj.mp d (□^[n]p) (by aesop);

@[simp]
lemma multibox_cons_conj'! :  𝓢 ⊢! ⋀(□'^[n](p :: Γ)) ⟶ ⋀□'^[n]Γ := by
  apply conj'conj'_subset;
  simp_all;

@[simp]
lemma collect_multibox_conj'! : 𝓢 ⊢! ⋀□'^[n]Γ ⟶ □^[n]⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using dhyp! multiboxverum!;
  | hsingle => simp;
  | hcons p Γ h ih =>
    simp_all;
    exact imp_trans''! (imply_right_and! (generalConj'! (by simp)) (imp_trans''! (by simp) ih)) collect_multibox_and!;

@[simp]
lemma collect_box_conj'! : 𝓢 ⊢! ⋀(□'Γ) ⟶ □(⋀Γ) := collect_multibox_conj'! (n := 1)


def collect_multibox_or : 𝓢 ⊢ □^[n]p ⋎ □^[n]q ⟶ □^[n](p ⋎ q) := or₃'' (multibox_axiomK' $ multinec or₁) (multibox_axiomK' $ multinec or₂)
@[simp] lemma collect_multibox_or! : 𝓢 ⊢! □^[n]p ⋎ □^[n]q ⟶ □^[n](p ⋎ q) := ⟨collect_multibox_or⟩

def collect_box_or : 𝓢 ⊢ □p ⋎ □q ⟶ □(p ⋎ q) := collect_multibox_or (n := 1)
@[simp] lemma collect_box_or! : 𝓢 ⊢! □p ⋎ □q ⟶ □(p ⋎ q) := ⟨collect_box_or⟩

def collect_multibox_or' (h : 𝓢 ⊢ □^[n]p ⋎ □^[n]q) : 𝓢 ⊢ □^[n](p ⋎ q) := collect_multibox_or ⨀ h
lemma collect_multibox_or'! (h : 𝓢 ⊢! □^[n]p ⋎ □^[n]q) : 𝓢 ⊢! □^[n](p ⋎ q) := ⟨collect_multibox_or' h.some⟩

def collect_box_or' (h : 𝓢 ⊢ □p ⋎ □q) : 𝓢 ⊢ □(p ⋎ q) := collect_multibox_or' (n := 1) h
lemma collect_box_or'! (h : 𝓢 ⊢! □p ⋎ □q) : 𝓢 ⊢! □(p ⋎ q) := ⟨collect_box_or' h.some⟩


def collect_dia_or : 𝓢 ⊢ ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := by
  simp [StandardModalLogicalConnective.duality'];
  apply contra₁';
  apply deduct';
  apply demorgan₂';
  apply dniAnd';
  apply deductInv';
  exact impTrans'' (implyBoxDistribute' demorgan₃) distribute_box_and;
@[simp] lemma collect_dia_or! : 𝓢 ⊢! ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := ⟨collect_dia_or⟩

def collect_dia_or' (h : 𝓢 ⊢ ◇p ⋎ ◇q) : 𝓢 ⊢ ◇(p ⋎ q) := collect_dia_or ⨀ h
@[simp] lemma collect_dia_or'! (h : 𝓢 ⊢! ◇p ⋎ ◇q) : 𝓢 ⊢! ◇(p ⋎ q) := ⟨collect_dia_or' h.some⟩

-- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.
@[simp] lemma distribute_multidia_and!: 𝓢 ⊢! ◇^[n](p ⋏ q) ⟶ ◇^[n]p ⋏ ◇^[n]q := by
  suffices h : 𝓢 ⊢! ~(□^[n](~(p ⋏ q))) ⟶ ~(□^[n](~p)) ⋏ ~(□^[n](~q)) by
    exact imp_trans''! (imp_trans''! (and₁'! multidia_duality!) h) $ and_replace! (and₂'! multidia_duality!) (and₂'! multidia_duality!);
  apply FiniteContext.deduct'!;
  apply demorgan₃'!;
  apply FiniteContext.deductInv'!;
  apply contra₀'!;
  apply imp_trans''! collect_multibox_or! (imply_multibox_distribute'! demorgan₁!)

@[simp] lemma distribute_dia_and! : 𝓢 ⊢! ◇(p ⋏ q) ⟶ ◇p ⋏ ◇q := distribute_multidia_and! (n := 1)


-- TODO: `iffConjMultidiaMultidiaconj'` is computable but it's too slow, so leave it.
@[simp] lemma iff_conj'multidia_multidiaconj'! : 𝓢 ⊢! ◇^[n](⋀Γ) ⟶ ⋀(◇'^[n]Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using dhyp! verum!;
  | hsingle p => simp;
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

-- def distributeDiaAnd' (h : 𝓢 ⊢ ◇(p ⋏ q)) : 𝓢 ⊢ ◇p ⋏ ◇q := distributeDiaAnd ⨀ h
lemma distribute_dia_and'! (h : 𝓢 ⊢! ◇(p ⋏ q)) : 𝓢 ⊢! ◇p ⋏ ◇q := distribute_dia_and! ⨀ h

open StandardModalLogicalConnective (boxdot)

def boxdotAxiomK : 𝓢 ⊢ ⊡(p ⟶ q) ⟶ (⊡p ⟶ ⊡q) := by
  simp [boxdot]
  apply deduct';
  apply deduct;
  have d : [p ⋏ □p, (p ⟶ q) ⋏ □(p ⟶ q)] ⊢[𝓢] (p ⟶ q) ⋏ □(p ⟶ q) := FiniteContext.byAxm;
  exact and₃' ((and₁' d) ⨀ (and₁' (q := □p) (FiniteContext.byAxm))) <|
    (axiomK' $ and₂' d) ⨀ (and₂' (p := p) (FiniteContext.byAxm));
@[simp] lemma boxdot_axiomK! : 𝓢 ⊢! ⊡(p ⟶ q) ⟶ (⊡p ⟶ ⊡q) := ⟨boxdotAxiomK⟩

def boxdotAxiomT : 𝓢 ⊢ ⊡p ⟶ p := by exact and₁;
@[simp] lemma boxdot_axiomT! : 𝓢 ⊢! ⊡p ⟶ p := ⟨boxdotAxiomT⟩

def boxdotNec (d : 𝓢 ⊢ p) : 𝓢 ⊢ ⊡p := and₃' d (nec d)
lemma boxdot_nec! (d : 𝓢 ⊢! p) : 𝓢 ⊢! ⊡p := ⟨boxdotNec d.some⟩

def boxdotBox : 𝓢 ⊢ ⊡p ⟶ □p := by exact and₂;
lemma boxdot_box! : 𝓢 ⊢! ⊡p ⟶ □p := ⟨boxdotBox⟩

def BoxBoxdot_BoxDotbox : 𝓢 ⊢ □⊡p ⟶ ⊡□p := impTrans'' distribute_box_and (impId _)
lemma boxboxdot_boxdotbox : 𝓢 ⊢! □⊡p ⟶ ⊡□p := ⟨BoxBoxdot_BoxDotbox⟩

def axiomT [HasAxiomT 𝓢] : 𝓢 ⊢ □p ⟶ p := HasAxiomT.T _
@[simp] lemma axiomT! [HasAxiomT 𝓢] : 𝓢 ⊢! □p ⟶ p := ⟨axiomT⟩

instance [HasAxiomT 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ FiniteContext.of axiomT⟩
instance [HasAxiomT 𝓢] (Γ : Context F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ Context.of axiomT⟩

def axiomT' [HasAxiomT 𝓢] (h : 𝓢 ⊢ □p) : 𝓢 ⊢ p := axiomT ⨀ h
@[simp] lemma axiomT'! [HasAxiomT 𝓢] (h : 𝓢 ⊢! □p) : 𝓢 ⊢! p := ⟨axiomT' h.some⟩


def axiomB [HasAxiomB 𝓢] : 𝓢 ⊢ p ⟶ □◇p := HasAxiomB.B _
@[simp] lemma axiomB! [HasAxiomB 𝓢] : 𝓢 ⊢! p ⟶ □◇p := ⟨axiomB⟩

instance [HasAxiomB 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ FiniteContext.of axiomB⟩
instance [HasAxiomB 𝓢] (Γ : Context F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ Context.of axiomB⟩


def axiomD [HasAxiomD 𝓢] : 𝓢 ⊢ □p ⟶ ◇p := HasAxiomD.D _
@[simp] lemma axiomD! [HasAxiomD 𝓢] : 𝓢 ⊢! □p ⟶ ◇p := ⟨axiomD⟩

instance [HasAxiomD 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ FiniteContext.of axiomD⟩
instance [HasAxiomD 𝓢] (Γ : Context F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ Context.of axiomD⟩


def axiomFour [HasAxiomFour 𝓢] : 𝓢 ⊢ □p ⟶ □□p := HasAxiomFour.Four _
@[simp] lemma axiomFour! [HasAxiomFour 𝓢] : 𝓢 ⊢! □p ⟶ □□p := ⟨axiomFour⟩

instance [HasAxiomFour 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ FiniteContext.of axiomFour⟩
instance [HasAxiomFour 𝓢] (Γ : Context F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ Context.of axiomFour⟩

def imply_BoxBoxdot_Box: 𝓢 ⊢  □⊡p ⟶ □p := by
  simp [boxdot];
  exact impTrans'' distribute_box_and and₁
@[simp] lemma imply_boxboxdot_box : 𝓢 ⊢! □⊡p ⟶ □p := ⟨imply_BoxBoxdot_Box⟩

def iff_Box_BoxBoxdot [HasAxiomFour 𝓢] : 𝓢 ⊢ □p ⟷ □⊡p := by
  simp [boxdot];
  apply iffIntro;
  . exact impTrans'' (implyRightAnd (impId _) axiomFour) collect_box_and
  . exact imply_BoxBoxdot_Box;
@[simp] lemma iff_box_boxboxdot! [HasAxiomFour 𝓢] : 𝓢 ⊢! □p ⟷ □⊡p := ⟨iff_Box_BoxBoxdot⟩

def iff_Box_BoxdotBox [HasAxiomFour 𝓢] : 𝓢 ⊢ □p ⟷ ⊡□p := by
  simp [boxdot];
  apply iffIntro;
  . exact impTrans'' (implyRightAnd (impId _) axiomFour) (impId _)
  . exact and₁
@[simp] lemma iff_box_boxdotbox! [HasAxiomFour 𝓢] : 𝓢 ⊢! □p ⟷ ⊡□p := ⟨iff_Box_BoxdotBox⟩

def iff_Boxdot_BoxdotBoxdot [HasAxiomFour 𝓢] : 𝓢 ⊢ ⊡p ⟷ ⊡⊡p := by
  apply iffIntro;
  . exact implyRightAnd (impId _) (impTrans'' boxdotBox (and₁' iff_Box_BoxBoxdot));
  . exact and₁;
@[simp] lemma iff_boxdot_boxdotboxdot [HasAxiomFour 𝓢] : 𝓢 ⊢! ⊡p ⟷ ⊡⊡p := ⟨iff_Boxdot_BoxdotBoxdot⟩

def boxdotAxiomFour [HasAxiomFour 𝓢] : 𝓢 ⊢ ⊡p ⟶ ⊡⊡p := and₁' iff_Boxdot_BoxdotBoxdot
@[simp] lemma boxdot_axiomFour! [HasAxiomFour 𝓢] : 𝓢 ⊢! ⊡p ⟶ ⊡⊡p := ⟨boxdotAxiomFour⟩


def iff_box_boxdot [HasAxiomT 𝓢] [HasAxiomFour 𝓢] : 𝓢 ⊢ □p ⟷ ⊡p := by
  apply iffIntro;
  . exact implyRightAnd (axiomT) (impId _);
  . exact and₂;
@[simp] lemma iff_box_boxdot! [HasAxiomT 𝓢] [HasAxiomFour 𝓢] : 𝓢 ⊢! □p ⟷ ⊡p := ⟨iff_box_boxdot⟩

def axiomFive [HasAxiomFive 𝓢] : 𝓢 ⊢ ◇p ⟶ □◇p := HasAxiomFive.Five _
@[simp] lemma axiomFive! [HasAxiomFive 𝓢] : 𝓢 ⊢! ◇p ⟶ □◇p := ⟨axiomFive⟩

instance [HasAxiomFive 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩
instance [HasAxiomFive 𝓢] (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩


def axiomTc [HasAxiomTc 𝓢] : 𝓢 ⊢ p ⟶ □p := HasAxiomTc.Tc _
@[simp] lemma axiomTc! [HasAxiomTc 𝓢] : 𝓢 ⊢! p ⟶ □p := ⟨axiomTc⟩

instance [HasAxiomTc 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ FiniteContext.of axiomTc⟩
instance [HasAxiomTc 𝓢] (Γ : Context F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ Context.of axiomTc⟩

private def axiomFour_of_Tc [HasAxiomTc 𝓢]  : 𝓢 ⊢ Axioms.Four p := axiomTc
instance [HasAxiomTc 𝓢] : HasAxiomFour 𝓢 := ⟨fun _ ↦ axiomFour_of_Tc⟩




def axiomVer [HasAxiomVer 𝓢] : 𝓢 ⊢ □p := HasAxiomVer.Ver _
@[simp] lemma axiomVer! [HasAxiomVer 𝓢] : 𝓢 ⊢! □p := ⟨axiomVer⟩

instance [HasAxiomVer 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ FiniteContext.of axiomVer⟩
instance [HasAxiomVer 𝓢] (Γ : Context F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ Context.of axiomVer⟩

private def axiomTc_of_Ver [HasAxiomVer 𝓢] : 𝓢 ⊢ Axioms.Tc p := dhyp _ axiomVer
instance [HasAxiomVer 𝓢] : HasAxiomTc 𝓢 := ⟨fun _ ↦ axiomTc_of_Ver⟩

private def axiomL_of_Ver [HasAxiomVer 𝓢] : 𝓢 ⊢ Axioms.L p := dhyp _ axiomVer
instance [HasAxiomVer 𝓢] : HasAxiomL 𝓢 := ⟨fun _ ↦ axiomL_of_Ver⟩

-- axiomTriv : 𝓢 ⊢ p ⟶ □p はネセシテーションを無意味にするはず
-- instance [Necessitation 𝓢] (Γ : FiniteContext F 𝓢) (h : 𝓢 ⊢ Γ.ctx.conj ⟶ □Γ.ctx.conj) : Necessitation Γ := ⟨
--   by intro p hp; exact ofDef $ impTrans'' h (implyBoxDistribute' $ toDef hp);
-- ⟩


def axiomL [HasAxiomL 𝓢] : 𝓢 ⊢ □(□p ⟶ p) ⟶ □p := HasAxiomL.L _
@[simp] lemma axiomL! [HasAxiomL 𝓢] : 𝓢 ⊢! □(□p ⟶ p) ⟶ □p := ⟨axiomL⟩

instance [HasAxiomL 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ FiniteContext.of axiomL⟩
instance [HasAxiomL 𝓢] (Γ : Context F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ Context.of axiomL⟩

private def axiomFour_of_L [HasAxiomL 𝓢] : 𝓢 ⊢ Axioms.Four p := by
  dsimp [Axioms.Four];
  have : 𝓢 ⊢ p ⟶ (⊡□p ⟶ ⊡p) := by
    dsimp [boxdot];
    apply deduct';
    apply deduct;
    exact and₃' (FiniteContext.byAxm) (and₁' (q := □□p) $ FiniteContext.byAxm);
  have : 𝓢 ⊢ p ⟶ (□⊡p ⟶ ⊡p) := impTrans'' this (implyLeftReplace BoxBoxdot_BoxDotbox);
  exact impTrans'' (impTrans'' (implyBoxDistribute' this) axiomL) (implyBoxDistribute' $ and₂);
instance [HasAxiomL 𝓢] : HasAxiomFour 𝓢 := ⟨fun _ ↦ axiomFour_of_L⟩

def goedel2 [HasAxiomL 𝓢] : 𝓢 ⊢ (~(□⊥) ⟷ ~(□(~(□⊥))) : F) := by
  apply negReplaceIff';
  apply iffIntro;
  . apply implyBoxDistribute';
    exact efq;
  . exact impTrans'' (by
      apply implyBoxDistribute';
      exact and₁' neg_equiv;
    ) axiomL;
lemma goedel2! [HasAxiomL 𝓢] : 𝓢 ⊢! (~(□⊥) ⟷ ~(□(~(□⊥))) : F) := ⟨goedel2⟩

def goedel2'.mp [HasAxiomL 𝓢] : 𝓢 ⊢ (~(□⊥) : F) → 𝓢 ⊢ ~(□(~(□⊥)) : F) := by intro h; exact (and₁' goedel2) ⨀ h;
def goedel2'.mpr [HasAxiomL 𝓢] : 𝓢 ⊢ ~(□(~(□⊥)) : F) → 𝓢 ⊢ (~(□⊥) : F) := by intro h; exact (and₂' goedel2) ⨀ h;
lemma goedel2'! [HasAxiomL 𝓢] : 𝓢 ⊢! (~(□⊥) : F) ↔ 𝓢 ⊢! ~(□(~(□⊥)) : F) := ⟨λ ⟨h⟩ ↦ ⟨goedel2'.mp h⟩, λ ⟨h⟩ ↦ ⟨goedel2'.mpr h⟩⟩

def axiomH [HasAxiomH 𝓢] : 𝓢 ⊢ □(□p ⟷ p) ⟶ □p := HasAxiomH.H _
@[simp] lemma axiomH! [HasAxiomH 𝓢] : 𝓢 ⊢! □(□p ⟷ p) ⟶ □p := ⟨axiomH⟩

instance [HasAxiomH 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ FiniteContext.of axiomH⟩
instance [HasAxiomH 𝓢] (Γ : Context F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ Context.of axiomH⟩

alias loeb := LoebRule.loeb
lemma loeb! [LoebRule 𝓢] : 𝓢 ⊢! □p ⟶ p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨loeb hp⟩

alias henkin := HenkinRule.henkin
lemma henkin! [HenkinRule 𝓢] : 𝓢 ⊢! □p ⟷ p → 𝓢 ⊢! p := by rintro ⟨hp⟩; exact ⟨henkin hp⟩

private def axiomL_of_K4Loeb [HasAxiomFour 𝓢] [LoebRule 𝓢] : 𝓢 ⊢ Axioms.L p := by
  dsimp [Axioms.L];
  generalize e : □(□p ⟶ p) ⟶ □p = q;
  have d₁ : [□(□p ⟶ p), □q] ⊢[𝓢] □□(□p ⟶ p) ⟶ □□p := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₂ : [□(□p ⟶ p), □q] ⊢[𝓢] □□p ⟶ □p := FiniteContext.weakening (by aesop) $ deductInv' axiomK;
  have d₃ : 𝓢 ⊢ □(□p ⟶ p) ⟶ □□(□p ⟶ p) := axiomFour;
  have : 𝓢 ⊢ □q ⟶ q := by
    nth_rw 2 [←e]; apply deduct'; apply deduct;
    exact d₂ ⨀ (d₁ ⨀ ((of d₃) ⨀ (FiniteContext.byAxm)));
  exact loeb this;
instance [System.K4Loeb 𝓢] : HasAxiomL 𝓢 := ⟨fun _ ↦ axiomL_of_K4Loeb⟩

instance [HasAxiomFour 𝓢] [HenkinRule 𝓢]  : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ iffIntro (axiomK' $ nec h) axiomFour);

instance [HasAxiomFour 𝓢] [HasAxiomH 𝓢] : HenkinRule 𝓢 where
  henkin h := (and₁' h) ⨀ (axiomH ⨀ nec h);

private def axiomH_of_GL [HasAxiomL 𝓢] : 𝓢 ⊢ Axioms.H p := by
  exact impTrans'' (implyBoxDistribute' $ and₁) axiomL
instance [HasAxiomL 𝓢] : HasAxiomH 𝓢 := ⟨fun _ ↦ axiomH_of_GL⟩

end

end LO.System

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

lemma Necessitation.nec! : 𝓢 ⊢! p → 𝓢 ⊢! □p := by rintro ⟨hp⟩; exact ⟨nec hp⟩

def Necessitation.multinec : 𝓢 ⊢ p → 𝓢 ⊢ □^[n]p := by
  intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;

lemma Necessitation.multinec! : 𝓢 ⊢! p → 𝓢 ⊢! □^[n]p := by rintro ⟨hp⟩; exact ⟨multinec hp⟩


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
  | succ n ih => simpa using impTrans (axiomK' $ nec ih) (by apply axiomK);

@[simp] lemma multibox_axiomK! : 𝓢 ⊢! □^[n](p ⟶ q) ⟶ □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK⟩

def multibox_axiomK' (h : 𝓢 ⊢ □^[n](p ⟶ q)) : 𝓢 ⊢ □^[n]p ⟶ □^[n]q := multibox_axiomK ⨀ h
@[simp] lemma multibox_axiomK'! (h : 𝓢 ⊢! □^[n](p ⟶ q)) : 𝓢 ⊢! □^[n]p ⟶ □^[n]q := ⟨multibox_axiomK' h.some⟩

alias multiboxedImplyDistribute := multibox_axiomK'
alias multiboxed_imply_distribute! := multibox_axiomK'!


def boxIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ (□p ⟷ □q) := by
  apply iffIntro;
  . exact axiomK' $ nec $ conj₁' h;
  . exact axiomK' $ nec $ conj₂' h;
@[simp] lemma box_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □p ⟷ □q := ⟨boxIff' h.some⟩

def multiboxIff' (h : 𝓢 ⊢ p ⟷ q) : 𝓢 ⊢ □^[n]p ⟷ □^[n]q := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
@[simp] lemma multibox_iff! (h : 𝓢 ⊢! p ⟷ q) : 𝓢 ⊢! □^[n]p ⟷ □^[n]q := ⟨multiboxIff' h.some⟩

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


def multiboxDuality : 𝓢 ⊢ □^[n]p ⟷ ~(◇^[n](~p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp [StandardModalLogicalConnective.duality'];
    exact iffTrans (boxIff' ih) dn
@[simp] lemma multiboxDuality! : 𝓢 ⊢! □^[n]p ⟷ ~(◇^[n](~p)) := ⟨multiboxDuality⟩

def boxDuality : 𝓢 ⊢ □p ⟷ ~(◇~p) := multiboxDuality (n := 1)
@[simp] lemma boxDuality! : 𝓢 ⊢! □p ⟷ ~(◇~p) := ⟨boxDuality⟩

lemma multiboxDuality'! : 𝓢 ⊢! □^[n]p ↔ 𝓢 ⊢! ~(◇^[n](~p)) := by
  constructor;
  . intro h; exact (conj₁'! multiboxDuality!) ⨀ h;
  . intro h; exact (conj₂'! multiboxDuality!) ⨀ h;

lemma boxDuality'! : 𝓢 ⊢! □p ↔ 𝓢 ⊢! ~(◇~p) := multiboxDuality'! (n := 1)


def multidiaDuality : 𝓢 ⊢ ◇^[n]p ⟷ ~(□^[n](~p)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp [StandardModalLogicalConnective.duality'];
    apply neg_iff';
    apply boxIff';
    exact iffTrans (negIff' ih) (iffComm' dn)
@[simp] lemma multidiaDuality! : 𝓢 ⊢! ◇^[n]p ⟷ ~(□^[n](~p)) := ⟨multidiaDuality⟩

def diaDuality : 𝓢 ⊢ ◇p ⟷ ~(□~p) := multidiaDuality (n := 1)
@[simp] lemma diaDuality! : 𝓢 ⊢! ◇p ⟷ ~(□~p) := ⟨diaDuality⟩

lemma multidiaDuality'! : 𝓢 ⊢! ◇^[n]p ↔ 𝓢 ⊢! ~(□^[n](~p)) := by
  constructor;
  . intro h; exact (conj₁'! multidiaDuality!) ⨀ h;
  . intro h; exact (conj₂'! multidiaDuality!) ⨀ h;
lemma diaDuality'! : 𝓢 ⊢! ◇p ↔ 𝓢 ⊢! ~(□~p) := multidiaDuality'! (n := 1)


def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
@[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := ⟨multiboxverum⟩

def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
@[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := ⟨boxverum⟩


def implyMultiboxDistribute' (h : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ □^[n]p ⟶ □^[n]q := multibox_axiomK' $ multinec h
@[simp] lemma imply_multibox_distribute'! (h : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! □^[n]p ⟶ □^[n]q := ⟨implyMultiboxDistribute' h.some⟩

def implyBoxDistribute' (h : 𝓢 ⊢ p ⟶ q) : 𝓢 ⊢ □p ⟶ □q := implyMultiboxDistribute' (n := 1) h
@[simp] lemma imply_box_distribute'! (h : 𝓢 ⊢! p ⟶ q) : 𝓢 ⊢! □p ⟶ □q := ⟨implyBoxDistribute' h.some⟩


def distribute_multibox_and : 𝓢 ⊢ □^[n](p ⋏ q) ⟶ □^[n]p ⋏ □^[n]q := implyRightAnd (implyMultiboxDistribute' conj₁) (implyMultiboxDistribute' conj₂)
@[simp] lemma distribute_multibox_and! : 𝓢 ⊢! □^[n](p ⋏ q) ⟶ □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and⟩

def distribute_box_and : 𝓢 ⊢ □(p ⋏ q) ⟶ □p ⋏ □q := distribute_multibox_and (n := 1)
@[simp] lemma distribute_box_and! : 𝓢 ⊢! □(p ⋏ q) ⟶ □p ⋏ □q := ⟨distribute_box_and⟩

def distribute_multibox_and' (h : 𝓢 ⊢ □^[n](p ⋏ q)) : 𝓢 ⊢ □^[n]p ⋏ □^[n]q := distribute_multibox_and ⨀ h
@[simp] lemma distribute_multibox_and'! (d : 𝓢 ⊢! □^[n](p ⋏ q)) : 𝓢 ⊢! □^[n]p ⋏ □^[n]q := ⟨distribute_multibox_and' d.some⟩

def distribute_box_and' (h : 𝓢 ⊢ □(p ⋏ q)) : 𝓢 ⊢ □p ⋏ □q := distribute_multibox_and' (n := 1) h
@[simp] lemma distribute_box_and'! (d : 𝓢 ⊢! □(p ⋏ q)) : 𝓢 ⊢! □p ⋏ □q := ⟨distribute_box_and' d.some⟩


def collect_multibox_and : 𝓢 ⊢ □^[n]p ⋏ □^[n]q ⟶ □^[n](p ⋏ q) := by
  have d₁ : 𝓢 ⊢ □^[n]p ⟶ □^[n](q ⟶ p ⋏ q) := implyMultiboxDistribute' conj₃;
  have d₂ : 𝓢 ⊢ □^[n](q ⟶ p ⋏ q) ⟶ (□^[n]q ⟶ □^[n](p ⋏ q)) := multibox_axiomK;
  exact (conj₂' (andImplyIffImplyImply _ _ _)) ⨀ (impTrans d₁ d₂);
@[simp] lemma collect_multibox_and! : 𝓢 ⊢! □^[n]p ⋏ □^[n]q ⟶ □^[n](p ⋏ q) := ⟨collect_multibox_and⟩

def collect_box_and : 𝓢 ⊢ □p ⋏ □q ⟶ □(p ⋏ q) := collect_multibox_and (n := 1)
@[simp] lemma collect_box_and! : 𝓢 ⊢! □p ⋏ □q ⟶ □(p ⋏ q) := ⟨collect_box_and⟩

def collect_multibox_and' (h : 𝓢 ⊢ □^[n]p ⋏ □^[n]q) : 𝓢 ⊢ □^[n](p ⋏ q) := collect_multibox_and ⨀ h
@[simp] lemma collect_multibox_and'! (h : 𝓢 ⊢! □^[n]p ⋏ □^[n]q) : 𝓢 ⊢! □^[n](p ⋏ q) := ⟨collect_multibox_and' h.some⟩

def collect_box_and' (h : 𝓢 ⊢ □p ⋏ □q) : 𝓢 ⊢ □(p ⋏ q) := collect_multibox_and' (n := 1) h
@[simp] lemma collect_box_and'! (h : 𝓢 ⊢! □p ⋏ □q) : 𝓢 ⊢! □(p ⋏ q) := ⟨collect_box_and' h.some⟩


lemma multibox_conj'_iff! : 𝓢 ⊢! □^[n](Γ.conj') ↔ ∀ p ∈ Γ, 𝓢 ⊢! □^[n]p := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons p Γ h ih =>
    simp_all;
    constructor;
    . intro h;
      have := distribute_multibox_and'! h;
      constructor;
      . exact conj₁'! this;
      . exact ih.mp (conj₂'! this);
    . rintro ⟨h₁, h₂⟩;
      exact collect_multibox_and'! $ conj₃'! h₁ (ih.mpr h₂);
lemma box_conj'_iff! : 𝓢 ⊢! □(Γ.conj') ↔ ∀ p ∈ Γ, 𝓢 ⊢! □p := multibox_conj'_iff! (n := 1)


def collect_multibox_or : 𝓢 ⊢ □^[n]p ⋎ □^[n]q ⟶ □^[n](p ⋎ q) := disj₃'' (multibox_axiomK' $ multinec disj₁) (multibox_axiomK' $ multinec disj₂)
@[simp] lemma collect_multibox_or! : 𝓢 ⊢! □^[n]p ⋎ □^[n]q ⟶ □^[n](p ⋎ q) := ⟨collect_multibox_or⟩

def collect_box_or : 𝓢 ⊢ □p ⋎ □q ⟶ □(p ⋎ q) := collect_multibox_or (n := 1)
@[simp] lemma collect_box_or! : 𝓢 ⊢! □p ⋎ □q ⟶ □(p ⋎ q) := ⟨collect_box_or⟩

def collect_multibox_or' (h : 𝓢 ⊢ □^[n]p ⋎ □^[n]q) : 𝓢 ⊢ □^[n](p ⋎ q) := collect_multibox_or ⨀ h
@[simp] lemma collect_multibox_or'! (h : 𝓢 ⊢! □^[n]p ⋎ □^[n]q) : 𝓢 ⊢! □^[n](p ⋎ q) := ⟨collect_multibox_or' h.some⟩

def collect_box_or' (h : 𝓢 ⊢ □p ⋎ □q) : 𝓢 ⊢ □(p ⋎ q) := collect_multibox_or' (n := 1) h
@[simp] lemma collect_box_or'! (h : 𝓢 ⊢! □p ⋎ □q) : 𝓢 ⊢! □(p ⋎ q) := ⟨collect_box_or' h.some⟩


def collect_dia_or : 𝓢 ⊢ ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := by
  simp [StandardModalLogicalConnective.duality'];
  apply contra₁';
  apply deduct';
  apply demorgan₂';
  apply dniAnd';
  apply deductInv';
  exact impTrans (implyBoxDistribute' demorgan₃) distribute_box_and;
@[simp] lemma collect_dia_or! : 𝓢 ⊢! ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := ⟨collect_dia_or⟩

def collect_dia_or' (h : 𝓢 ⊢ ◇p ⋎ ◇q) : 𝓢 ⊢ ◇(p ⋎ q) := collect_dia_or ⨀ h
@[simp] lemma collect_dia_or'! (h : 𝓢 ⊢! ◇p ⋎ ◇q) : 𝓢 ⊢! ◇(p ⋎ q) := ⟨collect_dia_or' h.some⟩

/-
def collect_multidia_or : 𝓢 ⊢ ◇^[n]p ⋎ ◇^[n]q ⟶ ◇^[n](p ⋎ q) := by
  induction n with
  | zero => simp; apply impId;
  | succ n ih =>
    simp [StandardModalLogicalConnective.duality'];
    apply contra₁';
    apply deduct';
    apply demorgan₂';
    apply dniAnd';
    apply deductInv';
    exact impTrans (by apply demorgan₃;) distribute_box_and;
@[simp] lemma collect_dia_or! : 𝓢 ⊢! ◇p ⋎ ◇q ⟶ ◇(p ⋎ q) := ⟨collect_dia_or⟩
-/


/-　TODO: 証明済みだが，妙に時間がかかって原因が分からないため一旦コメントアウトしている．
def distributeDiaAnd : 𝓢 ⊢ ◇(p ⋏ q) ⟶ ◇p ⋏ ◇q := by
  simp only [StandardModalLogicalConnective.duality'];
  have : 𝓢 ⊢ ~(~(□~p) ⋏ ~(□~q)) ⟶ □~p ⋎ □~q := FiniteContext.deduct' $ orReplace' (demorgan₄' $ FiniteContext.byAxm (by simp)) dne dne;
  exact contra₂' $ impTrans (impTrans this collect_box_or) (implyBoxDistribute' demorgan₁);
@[simp] lemma distribute_dia_and! : 𝓢 ⊢! ◇(p ⋏ q) ⟶ ◇p ⋏ ◇q := ⟨distributeDiaAnd⟩

def distributeDiaAnd' (h : 𝓢 ⊢ ◇(p ⋏ q)) : 𝓢 ⊢ ◇p ⋏ ◇q := distributeDiaAnd ⨀ h
lemma distribute_dia_and'! (h : 𝓢 ⊢! ◇(p ⋏ q)) : 𝓢 ⊢! ◇p ⋏ ◇q := ⟨distributeDiaAnd' h.some⟩
-/


/-
lemma distribute_multidia_conj'! (d : 𝓢 ⊢! ◇^[n](Γ.conj')) : 𝓢 ⊢! (◇^[n]Γ).conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all;
  | hcons p Γ h ih => sorry;

lemma distribute_dia_conj'! (d : 𝓢 ⊢! ◇(Γ.conj')) : 𝓢 ⊢! (◇Γ).conj' := distribute_multidia_conj'! (n := 1) d
-/

lemma iff_conj'multibox_multiboxconj'! : 𝓢 ⊢! □^[n](Γ.conj') ↔ 𝓢 ⊢! (□^[n]Γ).conj' := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons p Γ h ih =>
    simp only [(List.conj'_cons_nonempty h)];
    have e := List.conj'_cons_nonempty (a := □^[n]p) (as := □^[n]Γ) (by simpa)
    constructor;
    . intro h;
      simp [e];
      have d := distribute_multibox_and'! h;
      exact conj₃'! (conj₁'! d) (ih.mp $ conj₂'! d);
    . intro h;
      simp [e] at h;
      exact collect_multibox_and'! $ conj₃'! (conj₁'! h) (ih.mpr $ conj₂'! h);

lemma imply_multiboxconj'_conj'multibox! : 𝓢 ⊢! List.conj' (□^[n]Γ) ⟶ □^[n]List.conj' Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp only [List.map_nil, List.conj'_nil]; exact dhyp! multiboxverum!;
  | hsingle => simp only [List.map_cons, List.map_nil, List.conj'_singleton, imp_id!, dn_collect_imply'!, dne'!];
  | hcons p Γ h ih =>
    simp [
      (List.conj'_cons_nonempty h),
      (List.conj'_cons_nonempty (a := □^[n]p) (as := □^[n]Γ) (by simpa)),
    ];
    exact imp_trans! (andReplaceRight! ih) collect_multibox_and!;


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


def axiomFive [HasAxiomFive 𝓢] : 𝓢 ⊢ ◇p ⟶ □◇p := HasAxiomFive.Five _
@[simp] lemma axiomFive! [HasAxiomFive 𝓢] : 𝓢 ⊢! ◇p ⟶ □◇p := ⟨axiomFive⟩

instance [HasAxiomFive 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩
instance [HasAxiomFive 𝓢] (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩


end LO.System

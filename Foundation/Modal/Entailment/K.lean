module

public import Foundation.Modal.Entailment.E

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} [Entailment.K 𝓢] {n : ℕ} {φ ψ ξ χ: F}


section E

variable [DecidableEq F]

-- TODO: move
lemma neg_congruence! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ∼φ ⭤ ∼ψ := by
  apply E!_intro;
  . apply contra! $ C_of_E_mpr! h;
  . apply contra! $ C_of_E_mp! h;


def box_regularity (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! □φ ➝ □ψ := by
  apply ?_ ⨀ nec h;
  exact axiomK;

omit [DecidableEq F] in
lemma box_regularity! : 𝓢 ⊢ φ ➝ ψ → 𝓢 ⊢ □φ ➝ □ψ := λ ⟨h⟩ => ⟨box_regularity h⟩


def box_congruence (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! □φ ⭤ □ψ := by
  apply E_intro
  . apply box_regularity; exact K_left h;
  . apply box_regularity; exact K_right h;

-- TODO: move
omit [DecidableEq F] in
lemma box_congruence! : 𝓢 ⊢ φ ⭤ ψ → 𝓢 ⊢ □φ ⭤ □ψ := λ ⟨h⟩ => ⟨box_congruence h⟩

-- TODO
instance : Entailment.RE 𝓢 where
  re a := box_congruence a

instance : Entailment.E 𝓢 where

lemma dia_congruence! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ◇φ ⭤ ◇ψ := by
  apply E!_replace (E!_symm $ dia_duality!) (E!_symm $ dia_duality!);
  apply neg_congruence!;
  apply box_congruence!;
  apply neg_congruence!;
  exact h;

end E


def boxItr_axiomK : 𝓢 ⊢! □^[n](φ ➝ ψ) ➝ □^[n]φ ➝ □^[n]ψ := by
  induction n with
  | zero => apply C_id;
  | succ n ih => simpa using C_trans (axiomK' $ nec ih) (by apply axiomK);
@[simp] lemma boxItr_axiomK! : 𝓢 ⊢ □^[n](φ ➝ ψ) ➝ □^[n]φ ➝ □^[n]ψ := ⟨boxItr_axiomK⟩

def boxItr_axiomK' (h : 𝓢 ⊢! □^[n](φ ➝ ψ)) : 𝓢 ⊢! □^[n]φ ➝ □^[n]ψ := boxItr_axiomK ⨀ h
@[simp] lemma boxItr_axiomK'! (h : 𝓢 ⊢ □^[n](φ ➝ ψ)) : 𝓢 ⊢ □^[n]φ ➝ □^[n]ψ := ⟨boxItr_axiomK' h.some⟩

alias boxItredImplyDistribute := boxItr_axiomK'
alias boxItred_imply_distribute! := boxItr_axiomK'!


def boxIff' (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! (□φ ⭤ □ψ) := by
  apply E_intro;
  . exact axiomK' $ nec $ K_left h;
  . exact axiomK' $ nec $ K_right h;
@[simp] lemma box_iff! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ □φ ⭤ □ψ := ⟨boxIff' h.some⟩

def boxItrIff' (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! □^[n]φ ⭤ □^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
@[simp] lemma boxItr_iff! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ □^[n]φ ⭤ □^[n]ψ := ⟨boxItrIff' h.some⟩


def boxItrverum : 𝓢 ⊢! (□^[n]⊤ : F) := multinec verum
@[simp] lemma boxItrverum! : 𝓢 ⊢ (□^[n]⊤ : F) := ⟨boxItrverum⟩

def boxverum : 𝓢 ⊢! (□⊤ : F) := boxItrverum (n := 1)
@[simp] lemma boxverum! : 𝓢 ⊢ (□⊤ : F) := ⟨boxverum⟩
instance : Entailment.HasAxiomN 𝓢 := ⟨boxverum⟩

def boxdotverum : 𝓢 ⊢! (⊡⊤ : F) := K_intro verum boxverum
@[simp] lemma boxdotverum! : 𝓢 ⊢ (⊡⊤ : F) := ⟨boxdotverum⟩

def implyMultiboxDistribute' (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! □^[n]φ ➝ □^[n]ψ := boxItr_axiomK' $ multinec h
lemma imply_boxItr_distribute'! (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ □^[n]φ ➝ □^[n]ψ := ⟨implyMultiboxDistribute' h.some⟩

def implyBoxDistribute' (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! □φ ➝ □ψ := implyMultiboxDistribute' (n := 1) h
lemma imply_box_distribute'! (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ □φ ➝ □ψ := ⟨implyBoxDistribute' h.some⟩

def collect_boxItr_and : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ ➝ □^[n](φ ⋏ ψ) := by
  have d₁ : 𝓢 ⊢! □^[n]φ ➝ □^[n](ψ ➝ φ ⋏ ψ) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢! □^[n](ψ ➝ φ ⋏ ψ) ➝ (□^[n]ψ ➝ □^[n](φ ⋏ ψ)) := boxItr_axiomK;
  exact (K_right (ECKCC)) ⨀ (C_trans d₁ d₂);
@[simp] lemma collect_boxItr_and! : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ ➝ □^[n](φ ⋏ ψ) := ⟨collect_boxItr_and⟩

def collect_box_and : 𝓢 ⊢! □φ ⋏ □ψ ➝ □(φ ⋏ ψ) := collect_boxItr_and (n := 1)
@[simp] lemma collect_box_and! : 𝓢 ⊢ □φ ⋏ □ψ ➝ □(φ ⋏ ψ) := ⟨collect_box_and⟩

instance : Entailment.HasAxiomC 𝓢 := ⟨collect_box_and⟩

def collect_boxItr_and' (h : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋏ ψ) := collect_boxItr_and ⨀ h
lemma collect_boxItr_and'! (h : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋏ ψ) := ⟨collect_boxItr_and' h.some⟩

def collect_box_and' (h : 𝓢 ⊢! □φ ⋏ □ψ) : 𝓢 ⊢! □(φ ⋏ ψ) := collect_boxItr_and' (n := 1) h
lemma collect_box_and'! (h : 𝓢 ⊢ □φ ⋏ □ψ) : 𝓢 ⊢ □(φ ⋏ ψ) := ⟨collect_box_and' h.some⟩

def collect_boxItr_or : 𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ ➝ □^[n](φ ⋎ ψ) := left_A_intro (boxItr_axiomK' $ multinec or₁) (boxItr_axiomK' $ multinec or₂)
@[simp] lemma collect_boxItr_or! : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ ➝ □^[n](φ ⋎ ψ) := ⟨collect_boxItr_or⟩

def collect_box_or : 𝓢 ⊢! □φ ⋎ □ψ ➝ □(φ ⋎ ψ) := collect_boxItr_or (n := 1)
@[simp] lemma collect_box_or! : 𝓢 ⊢ □φ ⋎ □ψ ➝ □(φ ⋎ ψ) := ⟨collect_box_or⟩

def collect_boxItr_or' (h : 𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋎ ψ) := collect_boxItr_or ⨀ h
lemma collect_boxItr_or'! (h : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋎ ψ) := ⟨collect_boxItr_or' h.some⟩

def collect_box_or' (h : 𝓢 ⊢! □φ ⋎ □ψ) : 𝓢 ⊢! □(φ ⋎ ψ) := collect_boxItr_or' (n := 1) h
lemma collect_box_or'! (h : 𝓢 ⊢ □φ ⋎ □ψ) : 𝓢 ⊢ □(φ ⋎ ψ) := ⟨collect_box_or' h.some⟩

variable [DecidableEq F]



def diaK' (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ◇φ ➝ ◇ψ := by
  apply C_trans ?_ diaDuality_mpr;
  apply C_trans diaDuality_mp ?_;
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  assumption;
lemma diaK'! (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ◇φ ➝ ◇ψ := ⟨diaK' h.some⟩

lemma diaK''! (h₁ : 𝓢 ⊢ φ ➝ ψ) (h₂ : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ◇ψ := (diaK'! h₁) ⨀ h₂

lemma CMultidiaMultidia_of_C (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ◇^[n]φ ➝ ◇^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih =>
    simp only [Dia.diaItr_succ];
    apply diaK'! ih;



def diaIff' (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! (◇φ ⭤ ◇ψ) := by
  apply E_trans diaDuality;
  apply K_symm;
  apply E_trans diaDuality;
  apply ENN_of_E;
  apply boxIff';
  apply ENN_of_E;
  apply K_symm;
  assumption;
@[simp] lemma dia_iff! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ◇φ ⭤ ◇ψ := ⟨diaIff' h.some⟩

def diaItrIff' (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ◇^[n]φ ⭤ ◇^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
@[simp] lemma diaItr_iff! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ◇^[n]φ ⭤ ◇^[n]ψ := ⟨diaItrIff' h.some⟩


@[simp]
lemma CNDiaBoxN! : 𝓢 ⊢ □(∼φ) ➝ ∼◇φ := by
  apply C!_trans boxDuality_mp!;
  apply contra!;
  apply diaK'!;
  simp;

lemma NDia_of_BoxN! (h : 𝓢 ⊢ □(∼φ)) : 𝓢 ⊢ ∼◇φ := CNDiaBoxN! ⨀ h

lemma boxItr_duality'! : 𝓢 ⊢ □^[n]φ ↔ 𝓢 ⊢ ∼(◇^[n](∼φ)) := by
  constructor;
  . intro h; exact (K!_left boxItr_duality!) ⨀ h;
  . intro h; exact (K!_right boxItr_duality!) ⨀ h;

lemma box_duality'! : 𝓢 ⊢ □φ ↔ 𝓢 ⊢ ∼(◇(∼φ)) := boxItr_duality'! (n := 1)


def box_dni' (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □(∼∼φ) := box_dni ⨀ h
lemma box_dni'! (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □(∼∼φ) := ⟨box_dni' h.some⟩

@[simp] lemma negbox_dni! : 𝓢 ⊢ ∼□φ ➝ ∼□(∼∼φ) := by
  apply contra!;
  exact box_dne!;
lemma negbox_dni'! (h : 𝓢 ⊢ ∼□φ) : 𝓢 ⊢ ∼□(∼∼φ) := negbox_dni! ⨀ h

@[simp] lemma negbox_dne! : 𝓢 ⊢ ∼□(∼∼φ) ➝ ∼□φ := by
  apply contra!;
  exact box_dni!;
lemma negbox_dne'! (h : 𝓢 ⊢ ∼□(∼∼φ)) : 𝓢 ⊢ ∼□φ := negbox_dne! ⨀ h


def distribute_boxItr_and : 𝓢 ⊢! □^[n](φ ⋏ ψ) ➝ □^[n]φ ⋏ □^[n]ψ := right_K_intro (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)
@[simp] lemma distribute_boxItr_and! : 𝓢 ⊢ □^[n](φ ⋏ ψ) ➝ □^[n]φ ⋏ □^[n]ψ := ⟨distribute_boxItr_and⟩

def distribute_box_and : 𝓢 ⊢! □(φ ⋏ ψ) ➝ □φ ⋏ □ψ := distribute_boxItr_and (n := 1)
@[simp] lemma distribute_box_and! : 𝓢 ⊢ □(φ ⋏ ψ) ➝ □φ ⋏ □ψ := ⟨distribute_box_and⟩

def distribute_boxItr_and' (h : 𝓢 ⊢! □^[n](φ ⋏ ψ)) : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ := distribute_boxItr_and ⨀ h
lemma distribute_boxItr_and'! (d : 𝓢 ⊢ □^[n](φ ⋏ ψ)) : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ := ⟨distribute_boxItr_and' d.some⟩

def distribute_box_and' (h : 𝓢 ⊢! □(φ ⋏ ψ)) : 𝓢 ⊢! □φ ⋏ □ψ := distribute_boxItr_and' (n := 1) h
lemma distribute_box_and'! (d : 𝓢 ⊢ □(φ ⋏ ψ)) : 𝓢 ⊢ □φ ⋏ □ψ := ⟨distribute_box_and' d.some⟩

instance : Entailment.HasAxiomM 𝓢 := ⟨distribute_box_and⟩


def boxdotAxiomK : 𝓢 ⊢! ⊡(φ ➝ ψ) ➝ (⊡φ ➝ ⊡ψ) := by
  apply deduct';
  apply deduct;
  have d : [φ ⋏ □φ, (φ ➝ ψ) ⋏ □(φ ➝ ψ)] ⊢[𝓢]! (φ ➝ ψ) ⋏ □(φ ➝ ψ) := FiniteContext.byAxm;
  exact K_intro ((K_left d) ⨀ (K_left (ψ := □φ) (FiniteContext.byAxm))) <|
    (axiomK' $ K_right d) ⨀ (K_right (φ := φ) (FiniteContext.byAxm));
@[simp] lemma boxdot_axiomK! : 𝓢 ⊢ ⊡(φ ➝ ψ) ➝ (⊡φ ➝ ⊡ψ) := ⟨boxdotAxiomK⟩

def boxdotAxiomT : 𝓢 ⊢! ⊡φ ➝ φ := by exact and₁;
omit [DecidableEq F] in @[simp] lemma boxdot_axiomT! : 𝓢 ⊢ ⊡φ ➝ φ := ⟨boxdotAxiomT⟩

def boxdotNec (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊡φ := K_intro d (nec d)
omit [DecidableEq F] in lemma boxdot_nec! (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊡φ := ⟨boxdotNec d.some⟩

def boxdotBox : 𝓢 ⊢! ⊡φ ➝ □φ := by exact and₂;
omit [DecidableEq F] in lemma boxdot_box! : 𝓢 ⊢ ⊡φ ➝ □φ := ⟨boxdotBox⟩

def BoxBoxdot_BoxDotbox : 𝓢 ⊢! □⊡φ ➝ ⊡□φ := C_trans distribute_box_and (C_id)
lemma boxboxdot_boxdotbox : 𝓢 ⊢ □⊡φ ➝ ⊡□φ := ⟨BoxBoxdot_BoxDotbox⟩


section List

variable {Γ : List F}

@[simp]
lemma distribute_boxItr_conj! : 𝓢 ⊢ □^[n]⋀Γ ➝ ⋀(□^[n]'Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp only [List.conj₂_cons_nonempty h];
    have h₁ : 𝓢 ⊢ □^[n](φ ⋏ ⋀Γ) ➝ □^[n]φ := imply_boxItr_distribute'! $ and₁!;
    have h₂ : 𝓢 ⊢ □^[n](φ ⋏ ⋀Γ) ➝ ⋀(□^[n]'Γ) := C!_trans (imply_boxItr_distribute'! $ and₂!) ih;
    have := right_K!_intro h₁ h₂;
    exact C!_trans this $ by
      apply right_Conj₂!_intro;
      intro ψ hψ;
      replace hψ := List.LO.mem_boxItr_cons.mp hψ;
      rcases hψ with (rfl | hψ)
      . apply and₁!;
      . obtain ⟨ξ, hξ, rfl⟩ := List.LO.exists_of_mem_boxItr hψ;
        exact left_K!_intro_right $ left_Conj₂!_intro hψ;

@[simp]
lemma distribute_box_conj! : 𝓢 ⊢ □(⋀Γ) ➝ ⋀(□'Γ) := distribute_boxItr_conj! (n := 1)

lemma boxItrConj'_iff! : 𝓢 ⊢ □^[n]⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢ □^[n]φ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    suffices 𝓢 ⊢ □^[n](φ ⋏ ⋀Γ) ↔ 𝓢 ⊢ □^[n]φ ∧ ∀ ψ ∈ Γ, 𝓢 ⊢ □^[n]ψ by simp_all;
    constructor;
    . intro h;
      have := distribute_boxItr_and'! h;
      constructor;
      . exact K!_left this;
      . exact ih.mp (K!_right this);
    . rintro ⟨h₁, h₂⟩;
      exact collect_boxItr_and'! $ K!_intro h₁ (ih.mpr h₂);
  | _ => simp_all;
lemma boxConj'_iff! : 𝓢 ⊢ □⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢ □φ := boxItrConj'_iff! (n := 1)

lemma boxItrconj_of_conjboxItr! (d : 𝓢 ⊢ ⋀(□^[n]'Γ)) : 𝓢 ⊢ □^[n]⋀Γ := by
  apply boxItrConj'_iff!.mpr;
  intro φ hp;
  exact Conj₂!_iff_forall_provable.mp d (□^[n]φ) $ by grind;

@[simp]
lemma boxItr_cons_conjAux₁! :  𝓢 ⊢ ⋀(□^[n]'(φ :: Γ)) ➝ ⋀(□^[n]'Γ) := by
  apply CConj₂Conj₂!_of_subset;
  grind;

@[simp]
lemma boxItr_cons_conjAux₂! :  𝓢 ⊢ ⋀(□^[n]'(φ :: Γ)) ➝ □^[n]φ := by
  suffices 𝓢 ⊢ ⋀(□^[n]'(φ :: Γ)) ➝ ⋀(□^[n]'[φ]) by simpa;
  apply CConj₂Conj₂!_of_subset;
  grind;

@[simp]
lemma boxItr_cons_conj! :  𝓢 ⊢ ⋀(□^[n]'(φ :: Γ)) ➝ ⋀(□^[n]'Γ) ⋏ □^[n]φ :=
  right_K!_intro boxItr_cons_conjAux₁! boxItr_cons_conjAux₂!

@[simp]
lemma collect_boxItr_conj! : 𝓢 ⊢ ⋀(□^[n]'Γ) ➝ □^[n]⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using C!_of_conseq! boxItrverum!;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp_all only [List.LO.eq_boxItr_conn, List.conj₂_cons_nonempty h];
    apply C!_trans ?_ collect_boxItr_and!;
    rw [List.conj₂_cons_nonempty (show (□^[n]'Γ) ≠ [] by grind)]
    apply right_K!_intro;
    . exact and₁!;
    . apply C!_trans and₂! ih;

@[simp]
lemma collect_box_conj! : 𝓢 ⊢ ⋀(□'Γ) ➝ □(⋀Γ) := collect_boxItr_conj! (n := 1)

lemma contextual_nec! (h : Γ ⊢[𝓢] φ) : (□'Γ) ⊢[𝓢] □φ :=
  provable_iff.mpr $ C!_trans collect_box_conj! $ imply_box_distribute'! $ provable_iff.mp h

end List


section Finset

variable {Γ : Finset F}

@[simp]
lemma collect_boxItr_fconj! : 𝓢 ⊢ (□^[n]'Γ).conj ➝ □^[n](Γ.conj) := by
  refine C!_replace ?_ ?_ (collect_boxItr_conj! (n := n) (Γ := Γ.toList));
  . apply right_Conj₂!_intro
    intro φ hφ;
    apply left_Fconj!_intro;
    grind;
  . apply boxItr_axiomK'!
    apply multinec!;
    simp;

@[simp] lemma collect_box_fconj! : 𝓢 ⊢ (□'Γ).conj ➝ □(Γ.conj) := collect_boxItr_fconj! (n := 1)

end Finset


def diaOrInst₁ : 𝓢 ⊢! ◇φ ➝ ◇(φ ⋎ ψ) := by
  apply C_trans (K_left diaDuality);
  apply C_trans ?h (K_right diaDuality);
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  exact or₁;
@[simp] lemma dia_or_inst₁! : 𝓢 ⊢ ◇φ ➝ ◇(φ ⋎ ψ) := ⟨diaOrInst₁⟩

-- TODO: `diaItrOrInst₁`
@[simp] lemma diaItr_or_inst₁! : 𝓢 ⊢ ◇^[n]φ ➝ ◇^[n](φ ⋎ ψ) := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢ ◇◇^[n]φ ➝ ◇◇^[n](φ ⋎ ψ) by simpa;
    apply C!_trans (K!_left dia_duality!);
    apply C!_trans ?_ (K!_right dia_duality!);
    apply contra!;
    apply axiomK'!;
    apply nec!;
    apply contra!;
    exact ih;

def diaOrInst₂ : 𝓢 ⊢! ◇ψ ➝ ◇(φ ⋎ ψ) := by
  apply C_trans (K_left diaDuality);
  apply C_trans ?h (K_right diaDuality);
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  exact or₂;
@[simp] lemma dia_or_inst₂! : 𝓢 ⊢ ◇ψ ➝ ◇(φ ⋎ ψ) := ⟨diaOrInst₂⟩

-- TODO: `diaItrOrInst₂`
@[simp] lemma diaItr_or_inst₂! : 𝓢 ⊢ ◇^[n]ψ ➝ ◇^[n](φ ⋎ ψ) := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢ ◇◇^[n]ψ ➝ ◇◇^[n](φ ⋎ ψ) by simpa;
    apply C!_trans (K!_left dia_duality!);
    apply C!_trans ?_ (K!_right dia_duality!);
    apply contra!;
    apply axiomK'!;
    apply nec!;
    apply contra!;
    exact ih;

def collect_dia_or : 𝓢 ⊢! ◇φ ⋎ ◇ψ ➝ ◇(φ ⋎ ψ) := left_A_intro diaOrInst₁ diaOrInst₂
@[simp] lemma collect_dia_or! : 𝓢 ⊢ ◇φ ⋎ ◇ψ ➝ ◇(φ ⋎ ψ) := ⟨collect_dia_or⟩

def collect_dia_or' (h : 𝓢 ⊢! ◇φ ⋎ ◇ψ) : 𝓢 ⊢! ◇(φ ⋎ ψ) := collect_dia_or ⨀ h
@[simp] lemma collect_dia_or'! (h : 𝓢 ⊢ ◇φ ⋎ ◇ψ) : 𝓢 ⊢ ◇(φ ⋎ ψ) := ⟨collect_dia_or' h.some⟩

-- TODO: collectMultidiaOr
def collect_diaItr_or! : 𝓢 ⊢ ◇^[n]φ ⋎ ◇^[n]ψ ➝ ◇^[n](φ ⋎ ψ) := left_A!_intro diaItr_or_inst₁! diaItr_or_inst₂!

@[simp]
lemma distribute_diaItr_or! : 𝓢 ⊢ ◇^[n](φ ⋎ ψ) ➝ ◇^[n]φ ⋎ ◇^[n]ψ := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢ ◇◇^[n](φ ⋎ ψ) ➝ ◇◇^[n]φ ⋎ ◇◇^[n]ψ by simpa [Dia.diaItr_succ];
    apply C!_trans (K!_left dia_duality!);
    apply CN!_of_CN!_left;
    apply C!_trans CNAKNN!;
    suffices 𝓢 ⊢ □(∼◇^[n]φ ⋏ ∼◇^[n]ψ) ➝ □(∼◇^[n](φ ⋎ ψ)) by
      apply C!_trans ?_ this;
      apply C!_trans ?_ collect_box_and!;
      apply CKK!_of_C!_of_C!;
      repeat {
        apply C!_trans ?_ (K!_right $ box_duality!);
        apply contra!;
        apply diaK'!;
        exact dne!;
      };
    apply axiomK'!;
    apply nec!;
    apply C!_trans CKNNNA! ?_;
    apply contra!;
    exact ih;
@[simp] lemma distribute_dia_or! : 𝓢 ⊢ ◇(φ ⋎ ψ) ➝ ◇φ ⋎ ◇ψ := distribute_diaItr_or! (n := 1)

@[simp]
lemma not_dia_bot : 𝓢 ⊢ ∼◇^[n]⊥ := by
  refine contra! (K!_right $ diaItr_iff! iff_not_bot_top!) ⨀ ?_;
  . apply boxItr_duality'!.mp boxItrverum!;

-- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.
@[simp] lemma distribute_diaItr_and!: 𝓢 ⊢ ◇^[n](φ ⋏ ψ) ➝ ◇^[n]φ ⋏ ◇^[n]ψ := by
  suffices h : 𝓢 ⊢ ∼(□^[n](∼(φ ⋏ ψ))) ➝ ∼(□^[n](∼φ)) ⋏ ∼(□^[n](∼ψ)) by
    exact C!_trans (C!_trans (K!_left diaItr_duality!) h) $ CKK!_of_C!_of_C! (K!_right diaItr_duality!) (K!_right diaItr_duality!);
  apply FiniteContext.deduct'!;
  apply KNN!_of_NA!;
  apply FiniteContext.deductInv'!;
  apply contra!;
  apply C!_trans collect_boxItr_or! (imply_boxItr_distribute'! CANNNK!)

@[simp] lemma distribute_dia_and! : 𝓢 ⊢ ◇(φ ⋏ ψ) ➝ ◇φ ⋏ ◇ψ := distribute_diaItr_and! (n := 1)

-- def distributeDiaAnd' (h : 𝓢 ⊢! ◇(φ ⋏ ψ)) : 𝓢 ⊢! ◇φ ⋏ ◇ψ := distributeDiaAnd ⨀ h
lemma distribute_dia_and'! (h : 𝓢 ⊢ ◇(φ ⋏ ψ)) : 𝓢 ⊢ ◇φ ⋏ ◇ψ := distribute_dia_and! ⨀ h

section List

variable {Γ : List F}

@[simp]
lemma distribute_diaItr_disj! : 𝓢 ⊢ ◇^[n]⋁Γ ➝ ⋁(◇^[n]'Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply C_of_N; simp only [List.disj₂_nil, not_dia_bot];
  | hsingle => simp;
  | hcons φ Γ h ih =>
    rw [List.disj₂_cons_nonempty h, List.LO.eq_diaItr_conn, List.disj₂_cons_nonempty $ List.LO.not_nil_diaItr_of_not_nil h];
    apply C!_trans distribute_diaItr_or!;
    apply CAA!_of_C!_right;
    exact ih;

@[simp]
lemma distribute_dia_disj! : 𝓢 ⊢ ◇⋁Γ ➝ ⋁◇'Γ := by simpa using distribute_diaItr_disj! (n := 1)

-- TODO: `iffConjMultidiaMultidiaconj` is computable but it's too slow, so leave it.
@[simp] lemma iff_conjdiaItr_diaItrconj! : 𝓢 ⊢ ◇^[n](⋀Γ) ➝ ⋀(◇^[n]'Γ) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact C!_trans distribute_diaItr_and! $ by
      apply deduct'!;
      apply Conj₂!_iff_forall_provable.mpr;
      intro ψ hψ;
      replace hψ := List.LO.mem_diaItr_cons.mp hψ;
      rcases hψ with (rfl | hψ);
      . exact K!_left id!;
      . obtain ⟨ξ, hξ, rfl⟩ := List.LO.exists_of_mem_diaItr hψ;
        exact (Conj₂!_iff_forall_provable.mp $ (of'! ih) ⨀ (K!_right $ id!)) _ hψ;
  | _ => simp

end List


section Finset

variable {Γ : Finset F}

@[simp]
lemma distribute_diaItr_fdisj! : 𝓢 ⊢ ◇^[n]Γ.disj ➝ (◇^[n]'Γ).disj := by
  refine C!_replace ?_ ?_ (distribute_diaItr_disj! (n := n) (Γ := Γ.toList));
  . apply CMultidiaMultidia_of_C;
    simp;
  . apply left_Disj₂!_intro
    intro φ hφ;
    apply right_Fdisj!_intro;
    exact Finset.LO.mem_diaItr_of_toList_diaItr hφ;

@[simp] lemma distribute_dia_fdisj! : 𝓢 ⊢ ◇Γ.disj ➝ (◇'Γ).disj := distribute_diaItr_fdisj! (n := 1)

end Finset



section

noncomputable def lemma_Grz₁ : 𝓢 ⊢! □φ ➝ □(□((φ ⋏ (□φ ➝ □□φ)) ➝ □(φ ⋏ (□φ ➝ □□φ))) ➝ (φ ⋏ (□φ ➝ □□φ))) := by
  let ψ := φ ⋏ (□φ ➝ □□φ);
  have    : 𝓢 ⊢! ((□φ ➝ □□φ) ➝ □φ) ➝ □φ := peirce
  have    : 𝓢 ⊢! (φ ➝ ((□φ ➝ □□φ) ➝ □φ)) ➝ (φ ➝ □φ) := CCC_of_C_right this;
  have d₁ : 𝓢 ⊢! (ψ ➝ □φ) ➝ φ ➝ □φ := C_trans (K_left $ ECKCC) this;
  have    : 𝓢 ⊢! ψ ➝ φ := and₁;
  have    : 𝓢 ⊢! □ψ ➝ □φ := implyBoxDistribute' this;
  have d₂ : 𝓢 ⊢! (ψ ➝ □ψ) ➝ (ψ ➝ □φ) := CCC_of_C_right this;
  have    : 𝓢 ⊢! (ψ ➝ □ψ) ➝ φ ➝ □φ := C_trans d₂ d₁;
  have    : 𝓢 ⊢! □(ψ ➝ □ψ) ➝ □(φ ➝ □φ) := implyBoxDistribute' this;
  have    : 𝓢 ⊢! □(ψ ➝ □ψ) ➝ (□φ ➝ □□φ) := C_trans this axiomK;
  have    : 𝓢 ⊢! (φ ➝ □(ψ ➝ □ψ)) ➝ (φ ➝ (□φ ➝ □□φ)) := CCC_of_C_right this;
  have    : 𝓢 ⊢! φ ➝ (□(ψ ➝ □ψ) ➝ (φ ⋏ (□φ ➝ □□φ))) := by
    apply deduct';
    apply deduct;
    apply K_intro;
    . exact FiniteContext.byAxm;
    . exact (of this) ⨀ (C_of_conseq FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have    : 𝓢 ⊢! φ ➝ (□(ψ ➝ □ψ) ➝ ψ) := this;
  exact implyBoxDistribute' this;

lemma lemma_Grz₁! : 𝓢 ⊢ (□φ ➝ □(□((φ ⋏ (□φ ➝ □□φ)) ➝ □(φ ⋏ (□φ ➝ □□φ))) ➝ (φ ⋏ (□φ ➝ □□φ)))) := ⟨lemma_Grz₁⟩

end


section Boxlt

variable {n m : ℕ}

lemma boxLe_lt_succ! : 𝓢 ⊢ (□^≤[n + 1] φ) ➝ (□^≤[n] φ) := by
  apply CFconjFconj!_of_provable;
  intro ψ hψ;
  simp only [Finset.mem_image, Finset.mem_range] at hψ;
  obtain ⟨i, hi, rfl⟩ := hψ;
  apply Context.by_axm!
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio];
  use i;
  constructor;
  . omega;
  . simp;

lemma boxLe_lt_add! : 𝓢 ⊢ (□^≤[n + m] φ) ➝ (□^≤[n] φ) := by
  induction m with
  | zero => simp;
  | succ m ih =>
    rw [(show n + (m + 1) = n + m + 1 by rfl)];
    apply C!_trans boxLe_lt_succ! ih;

lemma boxLe_lt! (h : n ≥ m) : 𝓢 ⊢ (□^≤[n] φ) ➝ (□^≤[m] φ) := by
  convert boxLe_lt_add! (𝓢 := 𝓢) (n := m) (m := n - m) (φ := φ);
  omega;

lemma E_boxLe_succ! : 𝓢 ⊢ (□^≤[n + 1] φ) ⭤ (□^≤[n] φ) ⋏ (□^[(n + 1)] φ) := by
  apply E!_intro;
  . apply FConj_DT.mpr;
    apply K!_intro;
    . apply FConj_DT.mp;
      apply boxLe_lt!;
      omega;
    . apply Context.by_axm!;
      simp only [Finset.coe_image, Finset.coe_range, Box.boxItr_succ, Set.mem_image, Set.mem_Iio];
      use n + 1;
      constructor;
      . omega;
      . simp;
  . suffices 𝓢 ⊢ (□^≤[n]φ) ⋏ (Finset.conj {(□^[(n + 1)]φ)}) ➝ (□^≤[n + 1]φ) by simpa using this;
    dsimp only [Box.boxLe];
    convert CKFconjFconjUnion! (𝓢 := 𝓢) (Γ := Finset.range (n + 1) |>.image (λ i => □^[i] φ)) (Δ := {(□^[(n + 1)]φ)});
    ext ψ;
    grind;

lemma boxLe_regularity! (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (□^≤[n] φ) ➝ (□^≤[n] ψ) := by
  induction n with
  | zero => simpa;
  | succ n ih =>
    suffices 𝓢 ⊢ ((□^≤[n]φ) ⋏ (□^[(n + 1)]φ)) ➝ ((□^≤[n]ψ) ⋏ (□^[(n + 1)]ψ)) by
      apply C!_replace ?_ ?_ this;
      . apply C_of_E_mp! E_boxLe_succ!;
      . apply C_of_E_mpr! E_boxLe_succ!;
    apply CKK!_of_C!_of_C! ih $ imply_boxItr_distribute'! h;

-- TODO: better name
lemma boxLe_fconj_regularity_of_subset {Γ Δ : Finset _} (hs : Γ ⊆ Δ) : 𝓢 ⊢ (□^≤[n]Δ.conj) ➝ □^≤[n]Γ.conj := by
  apply boxLe_regularity!;
  apply CFConj_FConj!_of_subset hs;

end Boxlt



namespace Context

variable {X : Set F}

lemma provable_iff_boxed [InjectiveBox F] : (□'X) *⊢[𝓢] φ ↔ ∃ Δ : List F, (∀ ψ ∈ □'Δ, ψ ∈ □'X) ∧ (□'Δ) ⊢[𝓢] φ := by
  constructor;
  . intro h;
    obtain ⟨Γ,sΓ, hΓ⟩ := Context.provable_iff.mp h;
    use □⁻¹'Γ;
    constructor;
    . rintro ψ hψ;
      apply sΓ ψ;
      grind;
    . apply FiniteContext.provable_iff.mpr;
      apply C!_trans ?_ (FiniteContext.provable_iff.mp hΓ);
      apply CConj₂Conj₂!_of_subset;
      intro ψ hψ;
      obtain ⟨ξ, hξ, rfl⟩ := sΓ ψ hψ;
      grind;
  . rintro ⟨Δ, hΔ, h⟩;
    apply Context.provable_iff.mpr;
    use (□'Δ);

lemma nec! {Γ : Set F} (h : Γ *⊢[𝓢] φ) : (□'Γ) *⊢[𝓢] □φ := by
  apply Context.provable_iff.mpr;
  obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
  use (□'Δ);
  constructor;
  . grind;
  . exact contextual_nec! hΔ₂;

lemma box_regularity! (h : Γ *⊢[𝓢] φ ➝ ψ) : (□'Γ) *⊢[𝓢] □φ ➝ □ψ := by
  have H₁ := Context.nec! h;
  have H₂ : (□'Γ) *⊢[𝓢] □(φ ➝ ψ) ➝ (□φ ➝ □ψ) := by simp;
  exact H₂ ⨀ H₁;

lemma box_congruence! (h : Γ *⊢[𝓢] φ ⭤ ψ) : (□'Γ) *⊢[𝓢] □φ ⭤ □ψ := by
  apply E!_intro;
  . apply box_regularity!; exact C_of_E_mp! h;
  . apply box_regularity!; exact C_of_E_mpr! h;

end Context

end LO.Modal.Entailment
end

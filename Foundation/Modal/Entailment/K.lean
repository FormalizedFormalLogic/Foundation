import Foundation.Modal.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.K 𝓢]

def multibox_axiomK : 𝓢 ⊢ □^[n](φ ➝ ψ) ➝ □^[n]φ ➝ □^[n]ψ := by
  induction n with
  | zero => apply C_id;
  | succ n ih => simpa using C_trans (axiomK' $ nec ih) (by apply axiomK);
omit [DecidableEq F] in @[simp] lemma multibox_axiomK! : 𝓢 ⊢! □^[n](φ ➝ ψ) ➝ □^[n]φ ➝ □^[n]ψ := ⟨multibox_axiomK⟩

def multibox_axiomK' (h : 𝓢 ⊢ □^[n](φ ➝ ψ)) : 𝓢 ⊢ □^[n]φ ➝ □^[n]ψ := multibox_axiomK ⨀ h
omit [DecidableEq F] in @[simp] lemma multibox_axiomK'! (h : 𝓢 ⊢! □^[n](φ ➝ ψ)) : 𝓢 ⊢! □^[n]φ ➝ □^[n]ψ := ⟨multibox_axiomK' h.some⟩

alias multiboxedImplyDistribute := multibox_axiomK'
alias multiboxed_imply_distribute! := multibox_axiomK'!


def boxIff' (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ (□φ ⭤ □ψ) := by
  apply E_intro;
  . exact axiomK' $ nec $ K_left h;
  . exact axiomK' $ nec $ K_right h;
omit [DecidableEq F] in @[simp] lemma box_iff! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! □φ ⭤ □ψ := ⟨boxIff' h.some⟩

def multiboxIff' (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ □^[n]φ ⭤ □^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using boxIff' ih;
omit [DecidableEq F] in @[simp] lemma multibox_iff! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! □^[n]φ ⭤ □^[n]ψ := ⟨multiboxIff' h.some⟩


def diaDuality_mp : 𝓢 ⊢ ◇φ ➝ ∼(□(∼φ)) := K_left diaDuality
omit [DecidableEq F] in @[simp] lemma diaDuality_mp! : 𝓢 ⊢! ◇φ ➝ ∼(□(∼φ)) := ⟨diaDuality_mp⟩

def diaDuality_mpr : 𝓢 ⊢ ∼(□(∼φ)) ➝ ◇φ := K_right diaDuality
omit [DecidableEq F] in @[simp] lemma diaDuality_mpr! : 𝓢 ⊢! ∼(□(∼φ)) ➝ ◇φ := ⟨diaDuality_mpr⟩

def diaDuality'.mp (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ∼(□(∼φ)) := (K_left diaDuality) ⨀ h
def diaDuality'.mpr (h : 𝓢 ⊢ ∼(□(∼φ))) : 𝓢 ⊢ ◇φ := (K_right diaDuality) ⨀ h

omit [DecidableEq F] in
lemma dia_duality'! : 𝓢 ⊢! ◇φ ↔ 𝓢 ⊢! ∼(□(∼φ)) := ⟨
  λ h => ⟨diaDuality'.mp h.some⟩,
  λ h => ⟨diaDuality'.mpr h.some⟩
⟩

def multiDiaDuality : 𝓢 ⊢ ◇^[n]φ ⭤ ∼(□^[n](∼φ)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp;
    apply E_trans $ diaDuality (φ := ◇^[n]φ);
    apply ENN_of_E;
    apply boxIff';
    apply E_intro;
    . exact contra_CN' $ K_right ih;
    . exact contra_CN $ K_left ih;
lemma multidia_duality! : 𝓢 ⊢! ◇^[n]φ ⭤ ∼(□^[n](∼φ)) := ⟨multiDiaDuality⟩

lemma multidia_duality'! : 𝓢 ⊢! ◇^[n]φ ↔ 𝓢 ⊢! ∼(□^[n](∼φ)) := by
  constructor;
  . intro h; exact (K!_left multidia_duality!) ⨀ h;
  . intro h; exact (K!_right multidia_duality!) ⨀ h;

def diaK' (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ◇φ ➝ ◇ψ := by
  apply C_trans ?_ diaDuality_mpr;
  apply C_trans diaDuality_mp ?_;
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  assumption;
lemma diaK'! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ◇φ ➝ ◇ψ := ⟨diaK' h.some⟩

def diaIff' (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ (◇φ ⭤ ◇ψ) := by
  apply E_trans diaDuality;
  apply K_symm;
  apply E_trans diaDuality;
  apply ENN_of_E;
  apply boxIff';
  apply ENN_of_E;
  apply K_symm;
  assumption;
@[simp] lemma dia_iff! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ◇φ ⭤ ◇ψ := ⟨diaIff' h.some⟩

def multidiaIff' (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ◇^[n]φ ⭤ ◇^[n]ψ := by
  induction n with
  | zero => simpa;
  | succ n ih => simpa using diaIff' ih;
@[simp] lemma multidia_iff! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ◇^[n]φ ⭤ ◇^[n]ψ := ⟨multidiaIff' h.some⟩


def multiboxDuality : 𝓢 ⊢ □^[n]φ ⭤ ∼(◇^[n](∼φ)) := by
  induction n with
  | zero => simp; apply dn;
  | succ n ih =>
    simp;
    apply E_trans (boxIff' ih);
    apply EN_of_EN_left;
    exact E_symm $ diaDuality;
@[simp] lemma multibox_duality! : 𝓢 ⊢! □^[n]φ ⭤ ∼(◇^[n](∼φ)) := ⟨multiboxDuality⟩

@[simp] lemma multibox_duality_mp! : 𝓢 ⊢! □^[n]φ ➝ ∼(◇^[n](∼φ)) := K!_left multibox_duality!
lemma multibox_duality_mp'! (h : 𝓢 ⊢! □^[n]φ) : 𝓢 ⊢! ∼(◇^[n](∼φ)) := multibox_duality_mp! ⨀ h

@[simp] lemma multibox_duality_mpr! : 𝓢 ⊢! ∼(◇^[n](∼φ)) ➝ □^[n]φ := K!_right multibox_duality!
lemma multibox_duality_mpr'! (h : 𝓢 ⊢! ∼(◇^[n](∼φ))) : 𝓢 ⊢! □^[n]φ := multibox_duality_mpr! ⨀ h

def boxDuality : 𝓢 ⊢ □φ ⭤ ∼(◇(∼φ)) := multiboxDuality (n := 1)
@[simp] lemma box_duality! : 𝓢 ⊢! □φ ⭤ ∼(◇(∼φ)) := ⟨boxDuality⟩

def boxDuality_mp : 𝓢 ⊢ □φ ➝ ∼(◇(∼φ)) := K_left boxDuality
@[simp] lemma boxDuality_mp! : 𝓢 ⊢! □φ ➝ ∼(◇(∼φ)) := ⟨boxDuality_mp⟩

def boxDuality_mp' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ ∼(◇(∼φ)) := boxDuality_mp ⨀ h
lemma boxDuality_mp'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! ∼(◇(∼φ)) := ⟨boxDuality_mp' h.some⟩

def boxDuality_mpr : 𝓢 ⊢ ∼(◇(∼φ)) ➝ □φ := K_right boxDuality
@[simp] lemma boxDuality_mpr! : 𝓢 ⊢! ∼(◇(∼φ)) ➝ □φ := ⟨boxDuality_mpr⟩

def boxDuality_mpr' (h : 𝓢 ⊢ ∼(◇(∼φ))) : 𝓢 ⊢ □φ := boxDuality_mpr ⨀ h
lemma boxDuality_mpr'! (h : 𝓢 ⊢! ∼(◇(∼φ))) : 𝓢 ⊢! □φ := ⟨boxDuality_mpr' h.some⟩

lemma multibox_duality'! : 𝓢 ⊢! □^[n]φ ↔ 𝓢 ⊢! ∼(◇^[n](∼φ)) := by
  constructor;
  . intro h; exact (K!_left multibox_duality!) ⨀ h;
  . intro h; exact (K!_right multibox_duality!) ⨀ h;

lemma box_duality'! : 𝓢 ⊢! □φ ↔ 𝓢 ⊢! ∼(◇(∼φ)) := multibox_duality'! (n := 1)


def box_dni : 𝓢 ⊢ □φ ➝ □(∼∼φ) := axiomK' $ nec dni
@[simp] lemma box_dni! : 𝓢 ⊢! □φ ➝ □(∼∼φ) := ⟨box_dni⟩

def box_dni' (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ □(∼∼φ) := box_dni ⨀ h
lemma box_dni'! (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! □(∼∼φ) := ⟨box_dni' h.some⟩

def box_dne : 𝓢 ⊢ □(∼∼φ) ➝ □φ := axiomK' $ nec dne
omit [DecidableEq F] in @[simp] lemma box_dne! : 𝓢 ⊢! □(∼∼φ) ➝ □φ := ⟨box_dne⟩

def box_dne' (h : 𝓢 ⊢ □(∼∼φ)): 𝓢 ⊢ □φ := box_dne ⨀ h
omit [DecidableEq F] in lemma box_dne'! (h : 𝓢 ⊢! □(∼∼φ)): 𝓢 ⊢! □φ := ⟨box_dne' h.some⟩

@[simp] lemma negbox_dni! : 𝓢 ⊢! ∼□φ ➝ ∼□(∼∼φ) := by
  apply contra!;
  exact box_dne!;
lemma negbox_dni'! (h : 𝓢 ⊢! ∼□φ) : 𝓢 ⊢! ∼□(∼∼φ) := negbox_dni! ⨀ h

@[simp] lemma negbox_dne! : 𝓢 ⊢! ∼□(∼∼φ) ➝ ∼□φ := by
  apply contra!;
  exact box_dni!;
lemma negbox_dne'! (h : 𝓢 ⊢! ∼□(∼∼φ)) : 𝓢 ⊢! ∼□φ := negbox_dne! ⨀ h

def multiboxverum : 𝓢 ⊢ (□^[n]⊤ : F) := multinec verum
omit [DecidableEq F] in @[simp] lemma multiboxverum! : 𝓢 ⊢! (□^[n]⊤ : F) := ⟨multiboxverum⟩

def boxverum : 𝓢 ⊢ (□⊤ : F) := multiboxverum (n := 1)
omit [DecidableEq F] in @[simp] lemma boxverum! : 𝓢 ⊢! (□⊤ : F) := ⟨boxverum⟩

def boxdotverum : 𝓢 ⊢ (⊡⊤ : F) := K_intro verum boxverum
omit [DecidableEq F] in @[simp] lemma boxdotverum! : 𝓢 ⊢! (⊡⊤ : F) := ⟨boxdotverum⟩

def implyMultiboxDistribute' (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ □^[n]φ ➝ □^[n]ψ := multibox_axiomK' $ multinec h
omit [DecidableEq F] in lemma imply_multibox_distribute'! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! □^[n]φ ➝ □^[n]ψ := ⟨implyMultiboxDistribute' h.some⟩

def implyBoxDistribute' (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ □φ ➝ □ψ := implyMultiboxDistribute' (n := 1) h
omit [DecidableEq F] in lemma imply_box_distribute'! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! □φ ➝ □ψ := ⟨implyBoxDistribute' h.some⟩


def distribute_multibox_and : 𝓢 ⊢ □^[n](φ ⋏ ψ) ➝ □^[n]φ ⋏ □^[n]ψ := right_K_intro (implyMultiboxDistribute' and₁) (implyMultiboxDistribute' and₂)
@[simp] lemma distribute_multibox_and! : 𝓢 ⊢! □^[n](φ ⋏ ψ) ➝ □^[n]φ ⋏ □^[n]ψ := ⟨distribute_multibox_and⟩

def distribute_box_and : 𝓢 ⊢ □(φ ⋏ ψ) ➝ □φ ⋏ □ψ := distribute_multibox_and (n := 1)
@[simp] lemma distribute_box_and! : 𝓢 ⊢! □(φ ⋏ ψ) ➝ □φ ⋏ □ψ := ⟨distribute_box_and⟩

def distribute_multibox_and' (h : 𝓢 ⊢ □^[n](φ ⋏ ψ)) : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ := distribute_multibox_and ⨀ h
lemma distribute_multibox_and'! (d : 𝓢 ⊢! □^[n](φ ⋏ ψ)) : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ := ⟨distribute_multibox_and' d.some⟩

def distribute_box_and' (h : 𝓢 ⊢ □(φ ⋏ ψ)) : 𝓢 ⊢ □φ ⋏ □ψ := distribute_multibox_and' (n := 1) h
lemma distribute_box_and'! (d : 𝓢 ⊢! □(φ ⋏ ψ)) : 𝓢 ⊢! □φ ⋏ □ψ := ⟨distribute_box_and' d.some⟩

lemma conj_cons! : 𝓢 ⊢! (φ ⋏ ⋀Γ) ⭤ ⋀(φ :: Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil =>
    simp;
    apply E!_intro;
    . simp;
    . exact right_K!_intro (by simp) (by simp);
  | _ => simp;

@[simp]
lemma distribute_multibox_conj! : 𝓢 ⊢! □^[n]⋀Γ ➝ ⋀□'^[n]Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty h];
    have h₁ : 𝓢 ⊢! □^[n](φ ⋏ ⋀Γ) ➝ □^[n]φ := imply_multibox_distribute'! $ and₁!;
    have h₂ : 𝓢 ⊢! □^[n](φ ⋏ ⋀Γ) ➝ ⋀□'^[n]Γ := C!_trans (imply_multibox_distribute'! $ and₂!) ih;
    have := right_K!_intro h₁ h₂;
    exact C!_trans this $ by
      apply right_Conj₂!_intro;
      intro ψ hψ;
      simp only [List.mem_cons] at hψ;
      rcases hψ with (rfl | hψ)
      . apply and₁!;
      . obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_multibox hψ;
        exact left_K!_intro_right $ left_Conj₂_intro! hψ;

@[simp] lemma distribute_box_conj! : 𝓢 ⊢! □(⋀Γ) ➝ ⋀(□'Γ) := distribute_multibox_conj! (n := 1)


def collect_multibox_and : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ ➝ □^[n](φ ⋏ ψ) := by
  have d₁ : 𝓢 ⊢ □^[n]φ ➝ □^[n](ψ ➝ φ ⋏ ψ) := implyMultiboxDistribute' and₃;
  have d₂ : 𝓢 ⊢ □^[n](ψ ➝ φ ⋏ ψ) ➝ (□^[n]ψ ➝ □^[n](φ ⋏ ψ)) := multibox_axiomK;
  exact (K_right (ECKCC _ _ _)) ⨀ (C_trans d₁ d₂);
omit [DecidableEq F] in @[simp] lemma collect_multibox_and! : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ ➝ □^[n](φ ⋏ ψ) := ⟨collect_multibox_and⟩

def collect_box_and : 𝓢 ⊢ □φ ⋏ □ψ ➝ □(φ ⋏ ψ) := collect_multibox_and (n := 1)
omit [DecidableEq F] in @[simp] lemma collect_box_and! : 𝓢 ⊢! □φ ⋏ □ψ ➝ □(φ ⋏ ψ) := ⟨collect_box_and⟩

def collect_multibox_and' (h : 𝓢 ⊢ □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋏ ψ) := collect_multibox_and ⨀ h
omit [DecidableEq F] in lemma collect_multibox_and'! (h : 𝓢 ⊢! □^[n]φ ⋏ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋏ ψ) := ⟨collect_multibox_and' h.some⟩

def collect_box_and' (h : 𝓢 ⊢ □φ ⋏ □ψ) : 𝓢 ⊢ □(φ ⋏ ψ) := collect_multibox_and' (n := 1) h
omit [DecidableEq F] in lemma collect_box_and'! (h : 𝓢 ⊢! □φ ⋏ □ψ) : 𝓢 ⊢! □(φ ⋏ ψ) := ⟨collect_box_and' h.some⟩


lemma multiboxConj'_iff! : 𝓢 ⊢! □^[n]⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢! □^[n]φ := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    simp_all;
    constructor;
    . intro h;
      have := distribute_multibox_and'! h;
      constructor;
      . exact K!_left this;
      . exact ih.mp (K!_right this);
    . rintro ⟨h₁, h₂⟩;
      exact collect_multibox_and'! $ K!_intro h₁ (ih.mpr h₂);
  | _ => simp_all;
lemma boxConj'_iff! : 𝓢 ⊢! □⋀Γ ↔ ∀ φ ∈ Γ, 𝓢 ⊢! □φ := multiboxConj'_iff! (n := 1)

lemma multiboxconj_of_conjmultibox! (d : 𝓢 ⊢! ⋀□'^[n]Γ) : 𝓢 ⊢! □^[n]⋀Γ := by
  apply multiboxConj'_iff!.mpr;
  intro φ hp;
  exact Conj₂!_iff_forall_provable.mp d (□^[n]φ) $ List.multibox_mem_of hp;

@[simp]
lemma multibox_cons_conjAux₁! :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ➝ ⋀□'^[n]Γ := by
  apply CConj₂Conj₂!_of_subset;
  simp_all;

@[simp]
lemma multibox_cons_conjAux₂! :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ➝ □^[n]φ := by
  suffices 𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ➝ ⋀□'^[n]([φ]) by simpa;
  apply CConj₂Conj₂!_of_subset;
  simp_all;


@[simp]
lemma multibox_cons_conj! :  𝓢 ⊢! ⋀(□'^[n](φ :: Γ)) ➝ ⋀□'^[n]Γ ⋏ □^[n]φ :=
  right_K!_intro multibox_cons_conjAux₁! multibox_cons_conjAux₂!

@[simp]
lemma collect_multibox_conj! : 𝓢 ⊢! ⋀□'^[n]Γ ➝ □^[n]⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simpa using C!_of_conseq! multiboxverum!;
  | hsingle => simp;
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    refine C!_trans (right_K!_intro (left_Conj₂_intro! ?_) (C!_trans ?_ ih)) collect_multibox_and!;
    . simp;
    . simp [List.multibox, List.multibox_nonempty h];

@[simp]
lemma collect_box_conj! : 𝓢 ⊢! ⋀(□'Γ) ➝ □(⋀Γ) := collect_multibox_conj! (n := 1)


def collect_multibox_or : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ ➝ □^[n](φ ⋎ ψ) := left_A_intro (multibox_axiomK' $ multinec or₁) (multibox_axiomK' $ multinec or₂)
omit [DecidableEq F] in @[simp] lemma collect_multibox_or! : 𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ ➝ □^[n](φ ⋎ ψ) := ⟨collect_multibox_or⟩

def collect_box_or : 𝓢 ⊢ □φ ⋎ □ψ ➝ □(φ ⋎ ψ) := collect_multibox_or (n := 1)
omit [DecidableEq F] in @[simp] lemma collect_box_or! : 𝓢 ⊢! □φ ⋎ □ψ ➝ □(φ ⋎ ψ) := ⟨collect_box_or⟩

def collect_multibox_or' (h : 𝓢 ⊢ □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢ □^[n](φ ⋎ ψ) := collect_multibox_or ⨀ h
omit [DecidableEq F] in lemma collect_multibox_or'! (h : 𝓢 ⊢! □^[n]φ ⋎ □^[n]ψ) : 𝓢 ⊢! □^[n](φ ⋎ ψ) := ⟨collect_multibox_or' h.some⟩

def collect_box_or' (h : 𝓢 ⊢ □φ ⋎ □ψ) : 𝓢 ⊢ □(φ ⋎ ψ) := collect_multibox_or' (n := 1) h
omit [DecidableEq F] in lemma collect_box_or'! (h : 𝓢 ⊢! □φ ⋎ □ψ) : 𝓢 ⊢! □(φ ⋎ ψ) := ⟨collect_box_or' h.some⟩


def diaOrInst₁ : 𝓢 ⊢ ◇φ ➝ ◇(φ ⋎ ψ) := by
  apply C_trans (K_left diaDuality);
  apply C_trans ?h (K_right diaDuality);
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  exact or₁;
@[simp] lemma dia_or_inst₁! : 𝓢 ⊢! ◇φ ➝ ◇(φ ⋎ ψ) := ⟨diaOrInst₁⟩

-- TODO: `multidiaOrInst₁`
@[simp] lemma multidia_or_inst₁! : 𝓢 ⊢! ◇^[n]φ ➝ ◇^[n](φ ⋎ ψ) := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢! ◇◇^[n]φ ➝ ◇◇^[n](φ ⋎ ψ) by simpa;
    apply C!_trans (K!_left dia_duality!);
    apply C!_trans ?_ (K!_right dia_duality!);
    apply contra!;
    apply axiomK'!;
    apply nec!;
    apply contra!;
    exact ih;

def diaOrInst₂ : 𝓢 ⊢ ◇ψ ➝ ◇(φ ⋎ ψ) := by
  apply C_trans (K_left diaDuality);
  apply C_trans ?h (K_right diaDuality);
  apply contra;
  apply axiomK';
  apply nec;
  apply contra;
  exact or₂;
@[simp] lemma dia_or_inst₂! : 𝓢 ⊢! ◇ψ ➝ ◇(φ ⋎ ψ) := ⟨diaOrInst₂⟩

-- TODO: `multidiaOrInst₂`
@[simp] lemma multidia_or_inst₂! : 𝓢 ⊢! ◇^[n]ψ ➝ ◇^[n](φ ⋎ ψ) := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢! ◇◇^[n]ψ ➝ ◇◇^[n](φ ⋎ ψ) by simpa;
    apply C!_trans (K!_left dia_duality!);
    apply C!_trans ?_ (K!_right dia_duality!);
    apply contra!;
    apply axiomK'!;
    apply nec!;
    apply contra!;
    exact ih;

def collect_dia_or : 𝓢 ⊢ ◇φ ⋎ ◇ψ ➝ ◇(φ ⋎ ψ) := left_A_intro diaOrInst₁ diaOrInst₂
@[simp] lemma collect_dia_or! : 𝓢 ⊢! ◇φ ⋎ ◇ψ ➝ ◇(φ ⋎ ψ) := ⟨collect_dia_or⟩

def collect_dia_or' (h : 𝓢 ⊢ ◇φ ⋎ ◇ψ) : 𝓢 ⊢ ◇(φ ⋎ ψ) := collect_dia_or ⨀ h
@[simp] lemma collect_dia_or'! (h : 𝓢 ⊢! ◇φ ⋎ ◇ψ) : 𝓢 ⊢! ◇(φ ⋎ ψ) := ⟨collect_dia_or' h.some⟩

-- TODO: collectMultidiaOr
def collect_multidia_or! : 𝓢 ⊢! ◇^[n]φ ⋎ ◇^[n]ψ ➝ ◇^[n](φ ⋎ ψ) := left_A!_intro multidia_or_inst₁! multidia_or_inst₂!

@[simp]
lemma distribute_multidia_or! : 𝓢 ⊢! ◇^[n](φ ⋎ ψ) ➝ ◇^[n]φ ⋎ ◇^[n]ψ := by
  induction n with
  | zero => simp;
  | succ n ih =>
    suffices 𝓢 ⊢! ◇◇^[n](φ ⋎ ψ) ➝ ◇◇^[n]φ ⋎ ◇◇^[n]ψ by simpa [Dia.multidia_succ];
    apply C!_trans (K!_left dia_duality!);
    apply contra_CN!';
    apply C!_trans CNAKNN!;
    suffices 𝓢 ⊢! □(∼◇^[n]φ ⋏ ∼◇^[n]ψ) ➝ □(∼◇^[n](φ ⋎ ψ)) by
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

lemma distribute_dia_or! : 𝓢 ⊢! ◇(φ ⋎ ψ) ➝ ◇φ ⋎ ◇ψ := distribute_multidia_or! (n := 1)

-- TODO: move
omit [DecidableEq F] in
lemma iff_top_left'! (h : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⭤ ⊤ := by
  apply E!_intro;
  . simp;
  . exact C!_of_conseq! h;

-- TODO: move
omit [DecidableEq F] in
lemma iff_symm'! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ψ ⭤ φ := by
  apply E!_intro;
  . exact K!_right h;
  . exact K!_left h;

-- TODO: move
omit [DecidableEq F] in
lemma iff_top_right! (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊤ ⭤ φ := iff_symm'! $ iff_top_left'! h

-- TODO: move
@[simp]
lemma iff_not_bot_top! : 𝓢 ⊢! ∼⊤ ⭤ ⊥ := by
  apply E!_intro;
  . apply contra_CN!';
    apply C!_of_conseq!;
    simp;
  . exact efq!;

@[simp]
lemma not_dia_bot : 𝓢 ⊢! ∼◇^[n]⊥ := by
  refine contra! (K!_right $ multidia_iff! iff_not_bot_top!) ⨀ ?_;
  . apply multibox_duality'!.mp multiboxverum!;

@[simp]
lemma distribute_multidia_disj! : 𝓢 ⊢! ◇^[n]⋁Γ ➝ ⋁◇'^[n]Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => apply C_of_N; simp only [List.disj₂_nil, not_dia_bot];
  | hsingle => simp;
  | hcons φ Γ h ih =>
    suffices 𝓢 ⊢! ◇^[n](φ ⋎ ⋁Γ) ➝ (◇^[n]φ ⋎ ⋁◇'^[n]Γ) by
      simpa [List.multidia, List.disj₂_cons_nonempty h, List.disj₂_cons_nonempty (List.multidia_nonempty h)];
    exact C!_trans distribute_multidia_or! $ CAA!_of_C!_right ih;

@[simp]
lemma distribute_dia_disj! : 𝓢 ⊢! ◇⋁Γ ➝ ⋁◇'Γ := by simpa using distribute_multidia_disj! (n := 1)

-- TODO: `distributeMultidiaAnd!` is computable but it's too slow, so leave it.
@[simp] lemma distribute_multidia_and!: 𝓢 ⊢! ◇^[n](φ ⋏ ψ) ➝ ◇^[n]φ ⋏ ◇^[n]ψ := by
  suffices h : 𝓢 ⊢! ∼(□^[n](∼(φ ⋏ ψ))) ➝ ∼(□^[n](∼φ)) ⋏ ∼(□^[n](∼ψ)) by
    exact C!_trans (C!_trans (K!_left multidia_duality!) h) $ CKK!_of_C!_of_C! (K!_right multidia_duality!) (K!_right multidia_duality!);
  apply FiniteContext.deduct'!;
  apply KNN!_of_NA!;
  apply FiniteContext.deductInv'!;
  apply contra!;
  apply C!_trans collect_multibox_or! (imply_multibox_distribute'! CANNNK!)

@[simp] lemma distribute_dia_and! : 𝓢 ⊢! ◇(φ ⋏ ψ) ➝ ◇φ ⋏ ◇ψ := distribute_multidia_and! (n := 1)

-- TODO: `iffConjMultidiaMultidiaconj` is computable but it's too slow, so leave it.
@[simp] lemma iff_conjmultidia_multidiaconj! : 𝓢 ⊢! ◇^[n](⋀Γ) ➝ ⋀(◇'^[n]Γ) := by
  induction Γ using List.induction_with_singleton with
  | hcons φ Γ h ih =>
    simp_all only [ne_eq, not_false_eq_true, List.conj₂_cons_nonempty];
    exact C!_trans distribute_multidia_and! $ by
      apply deduct'!;
      apply Conj₂!_iff_forall_provable.mpr;
      intro ψ hq;
      simp only [List.mem_cons] at hq;
      rcases hq with (rfl | hψ);
      . exact K!_left id!;
      . obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_multidia hψ;
        exact (Conj₂!_iff_forall_provable.mp $ (of'! ih) ⨀ (K!_right $ id!)) _ hψ;
  | _ => simp

-- def distributeDiaAnd' (h : 𝓢 ⊢ ◇(φ ⋏ ψ)) : 𝓢 ⊢ ◇φ ⋏ ◇ψ := distributeDiaAnd ⨀ h
lemma distribute_dia_and'! (h : 𝓢 ⊢! ◇(φ ⋏ ψ)) : 𝓢 ⊢! ◇φ ⋏ ◇ψ := distribute_dia_and! ⨀ h

def boxdotAxiomK : 𝓢 ⊢ ⊡(φ ➝ ψ) ➝ (⊡φ ➝ ⊡ψ) := by
  apply deduct';
  apply deduct;
  have d : [φ ⋏ □φ, (φ ➝ ψ) ⋏ □(φ ➝ ψ)] ⊢[𝓢] (φ ➝ ψ) ⋏ □(φ ➝ ψ) := FiniteContext.byAxm;
  exact K_intro ((K_left d) ⨀ (K_left (ψ := □φ) (FiniteContext.byAxm))) <|
    (axiomK' $ K_right d) ⨀ (K_right (φ := φ) (FiniteContext.byAxm));
@[simp] lemma boxdot_axiomK! : 𝓢 ⊢! ⊡(φ ➝ ψ) ➝ (⊡φ ➝ ⊡ψ) := ⟨boxdotAxiomK⟩

def boxdotAxiomT : 𝓢 ⊢ ⊡φ ➝ φ := by exact and₁;
omit [DecidableEq F] in @[simp] lemma boxdot_axiomT! : 𝓢 ⊢! ⊡φ ➝ φ := ⟨boxdotAxiomT⟩

def boxdotNec (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊡φ := K_intro d (nec d)
omit [DecidableEq F] in lemma boxdot_nec! (d : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊡φ := ⟨boxdotNec d.some⟩

def boxdotBox : 𝓢 ⊢ ⊡φ ➝ □φ := by exact and₂;
omit [DecidableEq F] in lemma boxdot_box! : 𝓢 ⊢! ⊡φ ➝ □φ := ⟨boxdotBox⟩

def BoxBoxdot_BoxDotbox : 𝓢 ⊢ □⊡φ ➝ ⊡□φ := C_trans distribute_box_and (C_id _)
lemma boxboxdot_boxdotbox : 𝓢 ⊢! □⊡φ ➝ ⊡□φ := ⟨BoxBoxdot_BoxDotbox⟩


noncomputable def lemma_Grz₁ : 𝓢 ⊢ □φ ➝ □(□((φ ⋏ (□φ ➝ □□φ)) ➝ □(φ ⋏ (□φ ➝ □□φ))) ➝ (φ ⋏ (□φ ➝ □□φ))) := by
  let ψ := φ ⋏ (□φ ➝ □□φ);
  have    : 𝓢 ⊢ ((□φ ➝ □□φ) ➝ □φ) ➝ □φ := peirce
  have    : 𝓢 ⊢ (φ ➝ ((□φ ➝ □□φ) ➝ □φ)) ➝ (φ ➝ □φ) := CCC_of_C_right this;
  have d₁ : 𝓢 ⊢ (ψ ➝ □φ) ➝ φ ➝ □φ := C_trans (K_left $ ECKCC φ (□φ ➝ □□φ) (□φ)) this;
  have    : 𝓢 ⊢ ψ ➝ φ := and₁;
  have    : 𝓢 ⊢ □ψ ➝ □φ := implyBoxDistribute' this;
  have d₂ : 𝓢 ⊢ (ψ ➝ □ψ) ➝ (ψ ➝ □φ) := CCC_of_C_right this;
  have    : 𝓢 ⊢ (ψ ➝ □ψ) ➝ φ ➝ □φ := C_trans d₂ d₁;
  have    : 𝓢 ⊢ □(ψ ➝ □ψ) ➝ □(φ ➝ □φ) := implyBoxDistribute' this;
  have    : 𝓢 ⊢ □(ψ ➝ □ψ) ➝ (□φ ➝ □□φ) := C_trans this axiomK;
  have    : 𝓢 ⊢ (φ ➝ □(ψ ➝ □ψ)) ➝ (φ ➝ (□φ ➝ □□φ)) := CCC_of_C_right this;
  have    : 𝓢 ⊢ φ ➝ (□(ψ ➝ □ψ) ➝ (φ ⋏ (□φ ➝ □□φ))) := by
    apply deduct';
    apply deduct;
    apply K_intro;
    . exact FiniteContext.byAxm;
    . exact (of this) ⨀ (C_of_conseq FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
  have    : 𝓢 ⊢ φ ➝ (□(ψ ➝ □ψ) ➝ ψ) := this;
  exact implyBoxDistribute' this;

lemma lemma_Grz₁! : 𝓢 ⊢! (□φ ➝ □(□((φ ⋏ (□φ ➝ □□φ)) ➝ □(φ ⋏ (□φ ➝ □□φ))) ➝ (φ ⋏ (□φ ➝ □□φ)))) := ⟨lemma_Grz₁⟩


lemma contextual_nec! (h : Γ ⊢[𝓢]! φ) : (□'Γ) ⊢[𝓢]! □φ :=
  provable_iff.mpr $ C!_trans collect_box_conj! $ imply_box_distribute'! $ provable_iff.mp h


namespace Context

variable {X : Set F}

lemma provable_iff_boxed : (□''X) *⊢[𝓢]! φ ↔ ∃ Δ : List F, (∀ ψ ∈ □'Δ, ψ ∈ □''X) ∧ (□'Δ) ⊢[𝓢]! φ := by
  constructor;
  . intro h;
    obtain ⟨Γ,sΓ, hΓ⟩ := Context.provable_iff.mp h;
    use □'⁻¹Γ;
    constructor;
    . rintro ψ hψ;
      apply sΓ ψ;
      obtain ⟨ξ, hξ, rfl⟩ := List.exists_of_box hψ;
      exact List.mem_cancel_multibox_premultibox hψ;
    . apply FiniteContext.provable_iff.mpr;
      apply C!_trans ?_ (FiniteContext.provable_iff.mp hΓ);
      apply CConj₂Conj₂!_of_subset;
      intro ψ hψ;
      obtain ⟨ξ, hξ, rfl⟩ := sΓ ψ hψ;
      apply List.mem_decancel_box_prebox;
      assumption;
  . rintro ⟨Δ, hΔ, h⟩;
    apply Context.provable_iff.mpr;
    use □'Δ;

end Context

end LO.Entailment

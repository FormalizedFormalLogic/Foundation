module

public import Foundation.Modal.Entailment.DiaDuality


@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} [Entailment.E 𝓢] {n : ℕ} {φ ψ ξ χ: F}

variable [DecidableEq F]

def multire {n} (h : 𝓢 ⊢! φ 🡘 ψ) : 𝓢 ⊢! □^[n]φ 🡘 □^[n]ψ := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq]; exact h;
  | succ n ih =>
    simp only [Box.boxItr_succ];
    apply re ih;
omit [DecidableEq F] in lemma multire! {n} (h : 𝓢 ⊢ φ 🡘 ψ) : 𝓢 ⊢ □^[n]φ 🡘 □^[n]ψ := ⟨multire h.some⟩

def multi_ELLNN! : 𝓢 ⊢! □^[n]φ 🡘 □^[n](∼∼φ) := multire dn
@[simp] lemma multi_ELLNN : 𝓢 ⊢ □^[n]φ 🡘 □^[n](∼∼φ) := ⟨multi_ELLNN!⟩

def ELLNN! : 𝓢 ⊢! □φ 🡘 □(∼∼φ) := multi_ELLNN! (n := 1)
@[simp] lemma ELLNN : 𝓢 ⊢ □φ 🡘 □(∼∼φ) := multi_ELLNN (n := 1)

def ILLNN! : 𝓢 ⊢! □φ 🡒 □(∼∼φ) := K_left ELLNN!
@[simp] lemma ILLNN : 𝓢 ⊢ □φ 🡒 □(∼∼φ) := ⟨ILLNN!⟩
alias box_dni := ILLNN!
alias box_dni! := ILLNN

def ILNNL! : 𝓢 ⊢! □(∼∼φ) 🡒 □φ := K_right ELLNN!
@[simp] lemma ILNNL : 𝓢 ⊢ □(∼∼φ) 🡒 □φ := ⟨ILNNL!⟩
alias box_dne := ILNNL!
alias box_dne! := ILNNL

def box_dne' (h : 𝓢 ⊢! □(∼∼φ)): 𝓢 ⊢! □φ := box_dne ⨀ h
@[grind →] lemma box_dne'! (h : 𝓢 ⊢ □(∼∼φ)): 𝓢 ⊢ □φ := ⟨box_dne' h.some⟩

def INMNL! : 𝓢 ⊢! ∼◇(∼φ) 🡒 □φ := CN_of_CN_left (C_trans (contra ILNNL!) INLNM!)
@[simp] lemma INMNL : 𝓢 ⊢ ∼◇(∼φ) 🡒 □φ := ⟨INMNL!⟩

def INLMN! : 𝓢 ⊢! ∼□φ 🡒 ◇(∼φ) := CN_of_CN_left INMNL!
@[simp] lemma INLMN : 𝓢 ⊢ ∼□φ 🡒 ◇(∼φ) := ⟨INLMN!⟩



def multiDiaDuality : 𝓢 ⊢! ◇^[n]φ 🡘 ∼(□^[n](∼φ)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq];
    apply dn;
  | succ n ih =>
    simp only [Dia.diaItr_succ, Box.boxItr_succ];
    apply E_trans $ diaDuality (φ := ◇^[n]φ);
    apply ENN_of_E;
    apply re;
    apply E_intro;
    . exact CN_of_CN_left $ K_right ih;
    . exact CN_of_CN_right $ K_left ih;
lemma diaItr_duality! : 𝓢 ⊢ ◇^[n]φ 🡘 ∼(□^[n](∼φ)) := ⟨multiDiaDuality⟩

def diaItrDuality_mp : 𝓢 ⊢! ◇^[n]φ 🡒 ∼(□^[n](∼φ)) := K_left multiDiaDuality
def diaDuality_mp : 𝓢 ⊢! ◇φ 🡒 ∼(□(∼φ)) := diaItrDuality_mp (n := 1)

def diaItrDuality_mpr : 𝓢 ⊢! ∼(□^[n](∼φ)) 🡒 ◇^[n]φ := K_right multiDiaDuality
def diaDuality_mpr : 𝓢 ⊢! ∼(□(∼φ)) 🡒 ◇φ := diaItrDuality_mpr (n := 1)

def diaDuality'.mp (h : 𝓢 ⊢! ◇φ) : 𝓢 ⊢! ∼(□(∼φ)) := (K_left diaDuality) ⨀ h
def diaDuality'.mpr (h : 𝓢 ⊢! ∼(□(∼φ))) : 𝓢 ⊢! ◇φ := (K_right diaDuality) ⨀ h

@[simp] lemma diaItr_duality!_mp : 𝓢 ⊢ ◇^[n]φ 🡒 ∼(□^[n](∼φ)) := C_of_E_mp! diaItr_duality!
@[simp] lemma dia_duality!_mp : 𝓢 ⊢ ◇φ 🡒 ∼(□(∼φ)) := diaItr_duality!_mp (n := 1)

@[simp] lemma diaItr_duality!_mpr : 𝓢 ⊢ ∼(□^[n](∼φ)) 🡒 ◇^[n]φ := C_of_E_mpr! diaItr_duality!
@[simp] lemma dia_duality!_mpr : 𝓢 ⊢ ∼(□(∼φ)) 🡒 ◇φ := diaItr_duality!_mpr (n := 1)

omit [DecidableEq F] in lemma dia_duality'! : 𝓢 ⊢ ◇φ ↔ 𝓢 ⊢ ∼(□(∼φ)) := ⟨λ h => ⟨diaDuality'.mp h.some⟩, λ h => ⟨diaDuality'.mpr h.some⟩⟩

lemma diaItr_duality'! : 𝓢 ⊢ ◇^[n]φ ↔ 𝓢 ⊢ ∼(□^[n](∼φ)) := by
  constructor;
  . intro h; exact (K!_left diaItr_duality!) ⨀ h;
  . intro h; exact (K!_right diaItr_duality!) ⨀ h;


def boxItrDuality : 𝓢 ⊢! □^[n]φ 🡘 ∼(◇^[n](∼φ)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq];
    apply dn;
  | succ n ih =>
    simp only [Box.boxItr_succ, Dia.diaItr_succ];
    apply E_trans (re ih);
    apply EN_of_EN_left;
    exact E_symm $ diaDuality;
@[simp] lemma boxItr_duality! : 𝓢 ⊢ □^[n]φ 🡘 ∼(◇^[n](∼φ)) := ⟨boxItrDuality⟩

def boxItrDuality_mp: 𝓢 ⊢! □^[n]φ 🡒 ∼(◇^[n](∼φ)) := K_left boxItrDuality
def boxDuality_mp : 𝓢 ⊢! □φ 🡒 ∼(◇(∼φ)) := boxItrDuality_mp (n := 1)

def boxItrDuality_mpr: 𝓢 ⊢! ∼(◇^[n](∼φ)) 🡒 □^[n]φ := K_right boxItrDuality
def boxDuality_mpr : 𝓢 ⊢! ∼(◇(∼φ)) 🡒 □φ := boxItrDuality_mpr (n := 1)


@[simp] lemma boxItr_duality_mp! : 𝓢 ⊢ □^[n]φ 🡒 ∼(◇^[n](∼φ)) := K!_left boxItr_duality!
lemma boxItr_duality_mp'! (h : 𝓢 ⊢ □^[n]φ) : 𝓢 ⊢ ∼(◇^[n](∼φ)) := boxItr_duality_mp! ⨀ h

@[simp] lemma boxItr_duality_mpr! : 𝓢 ⊢ ∼(◇^[n](∼φ)) 🡒 □^[n]φ := K!_right boxItr_duality!
lemma boxItr_duality_mpr'! (h : 𝓢 ⊢ ∼(◇^[n](∼φ))) : 𝓢 ⊢ □^[n]φ := boxItr_duality_mpr! ⨀ h

def boxDuality : 𝓢 ⊢! □φ 🡘 ∼(◇(∼φ)) := boxItrDuality (n := 1)
@[simp] lemma box_duality! : 𝓢 ⊢ □φ 🡘 ∼(◇(∼φ)) := ⟨boxDuality⟩

@[simp] lemma boxDuality_mp! : 𝓢 ⊢ □φ 🡒 ∼(◇(∼φ)) := ⟨boxDuality_mp⟩

def boxDuality_mp' (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! ∼(◇(∼φ)) := boxDuality_mp ⨀ h
lemma boxDuality_mp'! (h : 𝓢 ⊢ □φ) : 𝓢 ⊢ ∼(◇(∼φ)) := ⟨boxDuality_mp' h.some⟩

@[simp] lemma boxDuality_mpr! : 𝓢 ⊢ ∼(◇(∼φ)) 🡒 □φ := ⟨boxDuality_mpr⟩

def boxDuality_mpr' (h : 𝓢 ⊢! ∼(◇(∼φ))) : 𝓢 ⊢! □φ := boxDuality_mpr ⨀ h
lemma boxDuality_mpr'! (h : 𝓢 ⊢ ∼(◇(∼φ))) : 𝓢 ⊢ □φ := ⟨boxDuality_mpr' h.some⟩

end LO.Modal.Entailment
end

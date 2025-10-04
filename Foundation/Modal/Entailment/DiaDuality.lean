import Foundation.Modal.Entailment.Basic

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} [Entailment.Cl 𝓢] [Entailment.HasDiaDuality 𝓢] {n : ℕ} {φ ψ ξ χ: F}


-- TODO: move to supplemental
omit [Entailment.HasDiaDuality 𝓢] in
section

lemma conj_cons! [DecidableEq F] : 𝓢 ⊢ (φ ⋏ ⋀Γ) ⭤ ⋀(φ :: Γ) := by
  induction Γ using List.induction_with_singleton with
  | hnil =>
    simp only [List.conj₂_nil, List.conj₂_singleton];
    apply E!_intro;
    . simp;
    . exact right_K!_intro (by simp) (by simp);
  | _ => simp;

lemma iff_top_left'! (h : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⭤ ⊤ := by
  apply E!_intro;
  . simp;
  . exact C!_of_conseq! h;

lemma iff_symm'! (h : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ψ ⭤ φ := by
  apply E!_intro;
  . exact K!_right h;
  . exact K!_left h;

lemma iff_top_right! (h : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊤ ⭤ φ := iff_symm'! $ iff_top_left'! h

@[simp]
lemma iff_not_bot_top! [DecidableEq F] : 𝓢 ⊢ ∼⊤ ⭤ ⊥ := by
  apply E!_intro;
  . apply CN!_of_CN!_left;
    apply C!_of_conseq!;
    simp;
  . exact efq!;

end


alias EMNLN! := diaDuality
alias EMNLN := diaDuality


def IMNLN! : 𝓢 ⊢! ◇φ ➝ ∼(□(∼φ)) := K_left diaDuality
@[simp] lemma IMNLN : 𝓢 ⊢ ◇φ ➝ ∼(□(∼φ)) := ⟨IMNLN!⟩

@[grind] lemma NLN_of_M (h : 𝓢 ⊢ ◇φ) : 𝓢 ⊢ ∼(□(∼φ)) := IMNLN ⨀ h


def INLNM! : 𝓢 ⊢! ∼(□(∼φ)) ➝ ◇φ := K_right diaDuality
@[simp] lemma INLNM : 𝓢 ⊢ ∼(□(∼φ)) ➝ ◇φ := ⟨INLNM!⟩

@[grind] lemma M_of_NLN (h : 𝓢 ⊢ ∼(□(∼φ))) : 𝓢 ⊢ ◇φ := INLNM ⨀ h

end LO.Modal.Entailment

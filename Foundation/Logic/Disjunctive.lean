import Foundation.Logic.HilbertStyle.Supplemental

namespace LO.System

variable {F : Type*} [LogicalConnective F]
variable {S : Type*} [System F S]

class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias disjunctive := Disjunctive.disjunctive

lemma iff_disjunctive {𝓢 : S}  : (Disjunctive 𝓢) ↔ ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ := by
  constructor;
  . apply Disjunctive.disjunctive;
  . exact λ d ↦ ⟨d⟩;

lemma iff_complete_disjunctive [DecidableEq F] {𝓢 : S} [System.Classical 𝓢] : (System.Complete 𝓢) ↔ (Disjunctive 𝓢) := by
  constructor;
  . intro hComp;
    apply iff_disjunctive.mpr;
    intro φ ψ hpq;
    rcases (hComp φ) with (hp | hnp);
    . left; assumption;
    . right; exact or₃'''! (efq_of_neg! hnp) imp_id! hpq;
  . intro hDisj φ;
    replace hDisj : ∀ {φ ψ}, 𝓢 ⊢! φ ⋎ ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ := iff_disjunctive.mp hDisj;
    exact @hDisj φ (∼φ) lem!;

end LO.System

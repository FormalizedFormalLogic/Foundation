import Logic.Logic.HilbertStyle.Supplemental

namespace LO.System

variable {F : Type*} [LogicalConnective F]
variable {S : Type*} [System F S]
variable [DecidableEq F]

class Disjunctive (𝓢 : S) : Prop where
  disjunctive : ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

lemma iff_disjunctive {𝓢 : S}  : (Disjunctive 𝓢) ↔ ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q := by
  constructor;
  . apply Disjunctive.disjunctive;
  . exact λ d ↦ ⟨d⟩;

lemma iff_complete_disjunctive {𝓢 : S} [System.Classical 𝓢] : (System.Complete 𝓢) ↔ (Disjunctive 𝓢) := by
  constructor;
  . intro hComp;
    apply iff_disjunctive.mpr;
    intro p q hpq;
    rcases (hComp p) with (hp | hnp);
    . left; assumption;
    . right; exact or₃'''! (efq_of_neg! hnp) imp_id! hpq;
  . intro hDisj p;
    replace hDisj : ∀ {p q}, 𝓢 ⊢! p ⋎ q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q := iff_disjunctive.mp hDisj;
    exact @hDisj p (∼p) lem!;

end LO.System

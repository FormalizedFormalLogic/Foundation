module

public import Foundation.Propositional.Hilbert.VF.Basic
public import Foundation.Propositional.Slash

@[expose] public section

namespace LO.Propositional

variable {H : HilbertVF α} {φ ψ χ : Formula α}

open Entailment.Corsi

namespace HilbertVF

lemma disjunctive_of_schema_aczelSlash (hs : ∀ {φ}, φ ∈ H → ∕ₐ[H] φ) : Entailment.Disjunctive H := by
  apply disjunctive_of_iff_aczelSlash_provable;
  intro φ;
  constructor;
  . intro h;
    induction φ with
    | hatom a => exact h;
    | hfalsum => contradiction;
    | hor φ ψ ihφ ihψ =>
      rcases h with h | h;
      . apply A_intro_left $ ihφ h;
      . apply A_intro_right $ ihψ h;
    | hand φ ψ ihφ ihψ => exact andIR (ihφ h.1) (ihψ h.2);
    | himp φ ψ ihφ ihψ => exact h.1;
  . intro h;
    replace h := HilbertVF.provable_of_mem_logic h;
    induction h with
    | orIntroL =>
      constructor;
      . exact orIntroL;
      . tauto;
    | orIntroR =>
      constructor;
      . exact orIntroR;
      . tauto;
    | andElimL =>
      constructor;
      . exact andElimL;
      . rintro ⟨_, _⟩; assumption;
    | andElimR =>
      constructor;
      . exact andElimR;
      . rintro ⟨_, _⟩; assumption;
    | impId =>
      constructor;
      . exact impId;
      . tauto;
    | distributeAndOr =>
      constructor;
      . exact distributeAndOr;
      . rintro ⟨hφ, (hψ | hψ)⟩ <;> tauto;
    | mdp ihφψ ihφ => apply ihφψ.2 ihφ;
    | af ihφ =>
      constructor;
      . apply af; assumption;
      . tauto;
    | efq =>
      constructor;
      . exact efq;
      . tauto;
    | ruleD ih₁ ih₂ =>
      constructor;
      . apply ruleD <;> assumption;
      . rintro (h | h) <;> grind;
    | ruleC ih₁ ih₂ =>
      constructor;
      . apply ruleC <;> assumption;
      . rintro h; constructor <;> grind;
    | ruleI ih₁ ih₂ =>
      constructor;
      . apply ruleI <;> assumption;
      . grind;
    | axm => apply hs; assumption;

attribute [grind .] Entailment.verum!

instance VF.Disjunctive : Entailment.Disjunctive (HilbertVF.VF : HilbertVF α) := HilbertVF.disjunctive_of_schema_aczelSlash $ by tauto;
instance VF_Ser.Disjunctive : Entailment.Disjunctive (HilbertVF.VF_Ser : HilbertVF α) := HilbertVF.disjunctive_of_schema_aczelSlash $ by
  rintro φ ⟨rfl⟩;
  apply AczelSlash.def_neg.mpr;
  grind;

end HilbertVF

end LO.Propositional
end

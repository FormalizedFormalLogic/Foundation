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
    induction h with
    | ruleI => grind [C_trans]
    | _ => grind;

attribute [grind .] Entailment.verum!

instance VF.Disjunctive : Entailment.Disjunctive (HilbertVF.VF : HilbertVF α) := HilbertVF.disjunctive_of_schema_aczelSlash $ by tauto;
instance VF_Ser.Disjunctive : Entailment.Disjunctive (HilbertVF.VF_Ser : HilbertVF α) := HilbertVF.disjunctive_of_schema_aczelSlash $ by
  rintro φ ⟨rfl⟩;
  apply AczelSlash.def_neg.mpr;
  grind;

end HilbertVF

end LO.Propositional
end

module

public import Foundation.Propositional.Hilbert.F.Basic
public import Foundation.Propositional.Slash

@[expose] public section

namespace LO.Propositional

variable {H : HilbertF α} {φ ψ χ : Formula α}

open Entailment.Corsi

namespace HilbertF

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
    | axiomI => grind [C_trans]
    | _ => grind;

attribute [grind .] Entailment.verum!

lemma slashable_axiomSer [Entailment.HasAxiomSer H] : ∕ₐ[H] ((Axioms.Ser)) := by
  apply AczelSlash.def_neg.mpr;
  grind
lemma slashable_axiomTra1 [Entailment.HasAxiomTra1 H] : ∕ₐ[H] ((Axioms.Tra1 φ ψ χ)) := by grind
lemma slashable_axiomRfl [Entailment.HasAxiomRfl H] : ∕ₐ[H] ((Axioms.Rfl φ ψ)) := by grind
lemma slashable_propvar_axiomHrd (h : ∀ a, H ⊢ #a 🡒 ⊤ 🡒 #a) : ∕ₐ[H] (Axioms.Hrd #a) := by grind;

attribute [grind .]
  slashable_axiomSer
  slashable_axiomTra1
  slashable_axiomRfl
  slashable_propvar_axiomHrd

instance F.Disjunctive : Entailment.Disjunctive (HilbertF.F : HilbertF α) := HilbertF.disjunctive_of_schema_aczelSlash $ by tauto;

instance F_Ser.Disjunctive : Entailment.Disjunctive (HilbertF.F_Ser : HilbertF α) := HilbertF.disjunctive_of_schema_aczelSlash $ by
  rintro φ ⟨_⟩;
  grind;

instance F_Rfl.Disjunctive : Entailment.Disjunctive (HilbertF.F_Rfl : HilbertF α) := HilbertF.disjunctive_of_schema_aczelSlash $ by
  rintro φ ⟨_⟩;
  grind;

instance F_Tra1.Disjunctive : Entailment.Disjunctive (HilbertF.F_Tra1 : HilbertF α) := HilbertF.disjunctive_of_schema_aczelSlash $ by
  rintro φ ⟨_⟩;
  grind;

end HilbertF

end LO.Propositional
end

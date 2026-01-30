module
public import Foundation.Propositional.Entailment.Corsi.WF

@[expose] public section

namespace LO.Propositional

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

protected class F (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasDistributeAndOr 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomC 𝓢,
  Entailment.HasAxiomD 𝓢,
  Entailment.HasAxiomI 𝓢,
  Entailment.HasAxiomVerum 𝓢,
  Entailment.HasAxiomEFQ 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢

-- TODO: unify old
namespace Corsi

variable [Entailment.F 𝓢]

instance : RuleD 𝓢 where
  ruleD! {φ ψ χ} h₁ h₂ := by
    refine axiomD! ⨀ ?_
    apply andIR! <;> assumption;

instance : RuleC 𝓢 where
  ruleC! {φ ψ χ} h₁ h₂ := by
    refine axiomC! ⨀ ?_
    apply andIR! <;> assumption;

instance : RuleI 𝓢 where
  ruleI! {φ ψ χ} h₁ h₂ := by
    refine (axiomI! (ψ := ψ)) ⨀ ?_;
    apply andIR! <;> assumption;

instance : RuleRestall 𝓢 where
  restall! {φ ψ χ ξ} h₁ h₂ := by
    apply ruleI! (ψ := (φ ➝ χ) ⋏ (χ ➝ ξ)) ?_ axiomI!;
    apply ruleC!;
    . apply ruleI! (ψ := (φ ➝ ψ) ⋏ (ψ ➝ χ)) ?_ axiomI!;
      apply ruleC!;
      . apply af! h₁;
      . apply impId!;
    . apply af! h₂;

instance : RuleE 𝓢 where
  ruleE! h₁ h₂ := by
    apply andIR!;
    . apply restall! (K_Elim_right! h₁) (K_Elim_left! h₂);
    . apply restall! (K_Elim_left! h₁) (K_Elim_right! h₂);

end Corsi



end Entailment


end LO.Propositional

end

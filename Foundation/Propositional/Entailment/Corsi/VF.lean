import Foundation.Propositional.Entailment.Corsi.Basic

namespace LO.Propositional

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

protected class VF (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasCollectOrAnd 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomVerum 𝓢,
  Entailment.HasAxiomEFQ 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢,
  Entailment.RuleC 𝓢,
  Entailment.RuleD 𝓢,
  Entailment.RuleI 𝓢

-- TODO: unify old
namespace Corsi

variable [Entailment.VF 𝓢]

/-
instance : Entailment.AndIntroRule 𝓢 where
  andIR! hφ hψ := by sorry;

-/

end Corsi



end Entailment


end LO.Propositional

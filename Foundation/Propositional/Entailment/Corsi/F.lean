import Foundation.Propositional.Entailment.Corsi.Basic

namespace LO.Propositional

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}



namespace Entailment

protected class F (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasDistributeAndOr 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomC 𝓢,
  Entailment.HasAxiomD 𝓢,
  Entailment.HasAxiomI 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢

end Entailment


end LO.Propositional

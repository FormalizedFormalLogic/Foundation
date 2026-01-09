module
import Foundation.InterpretabilityLogic.Entailment.IL_W
import Foundation.InterpretabilityLogic.Entailment.IL_KW2

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_KW1Zero (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomKW1Zero 𝓢

variable [Entailment.IL_KW1Zero 𝓢]

instance : Entailment.HasAxiomKW2 𝓢 where
  axiomKW2! {_ _} := C_trans (R2! and₂) axiomKW1Zero!

end LO.InterpretabilityLogic.Entailment

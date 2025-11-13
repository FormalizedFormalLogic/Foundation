import Foundation.InterpretabilityLogic.Entailment.ILR
import Foundation.InterpretabilityLogic.Entailment.ILW

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILRStar (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, Entailment.HasAxiomRStar 𝓢

variable [Entailment.ILRStar 𝓢]

instance : HasAxiomW 𝓢 where
  axiomW! {φ ψ} := by

    sorry;

instance : Entailment.ILW 𝓢 where


instance : HasAxiomR 𝓢 where
  axiomR! {φ ψ χ} := by

    sorry;

instance : Entailment.ILR 𝓢 where

end LO.InterpretabilityLogic.Entailment

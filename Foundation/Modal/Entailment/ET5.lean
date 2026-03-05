module

public import Foundation.Modal.Entailment.ETB
public import Foundation.Modal.Entailment.AxiomGeach

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} {n : ℕ} {φ ψ ξ χ: F}

protected class ET5 (𝓢 : S) extends Entailment.E 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢
instance [Entailment.ET5 𝓢] : Entailment.ET 𝓢 where
instance [Entailment.ET5 𝓢] : Entailment.E5 𝓢 where


variable [Entailment.ET5 𝓢]
variable [DecidableEq F]

namespace ET5

instance : Entailment.HasAxiomB 𝓢 := ⟨C_trans diaTc axiomFive⟩

instance : Entailment.ETB 𝓢 where

instance : Entailment.EN 𝓢 where

instance : Entailment.HasAxiomPoint2 𝓢 := ⟨C_trans (C_trans axiomFiveDual! axiomT) axiomB⟩

instance : Entailment.HasAxiomFour 𝓢 := ⟨C_trans (C_trans axiomTDual! axiomFive) (K_left $ re $ K_intro axiomFiveDual! axiomTDual!)⟩
end ET5


end LO.Modal.Entailment
end

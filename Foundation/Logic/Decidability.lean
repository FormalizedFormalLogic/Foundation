import Foundation.Logic.Entailment

namespace LO.Entailment

section

variable {F S : Type*} [Primcodable F] [Entailment F S]

variable (𝓢 : S)

class Decidable where
  dec : ComputablePred (theory 𝓢)

def Undecidable := ¬Decidable 𝓢

class EssentiallyUndecidable [LogicalConnective F] where
  essentially_undec : ∀ 𝓣 : S, 𝓢 ⪯ 𝓣 → Incomplete 𝓣 → Undecidable 𝓣

variable {𝓢}

lemma decidable_of_incomplete : Inconsistent 𝓢 → Decidable 𝓢 :=
  fun h ↦ ⟨by rw [h.theory_eq]; exact ComputablePred.const _⟩

end

end LO.Entailment

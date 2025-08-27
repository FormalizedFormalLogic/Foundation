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

class PrimrecLogicalConnective (F : Type*) [Primcodable F] extends LogicalConnective F where
  and : Primrec₂ fun φ ψ : F ↦ φ ⋏ ψ
  or : Primrec₂ fun φ ψ : F ↦ φ ⋎ ψ
  imply : Primrec₂ fun φ ψ : F ↦ φ ➝ ψ
  neg : Primrec fun φ : F ↦ ∼φ

section Craig's_trick

variable {F : Type*} [Primcodable F] [Entailment F (Set F)]



end Craig's_trick

end LO.Entailment

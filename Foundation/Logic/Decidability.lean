module

public import Foundation.Logic.Entailment
public import Foundation.Vorspiel.Computability

@[expose] public section

namespace FFL.Entailment

section

variable {F S : Type*} [Primcodable F] [Entailment S F]

variable (𝓢 : S)

class Decidable where
  dec : ComputablePred (· ∈ theory 𝓢)

def Undecidable := ¬Decidable 𝓢

class EssentiallyUndecidable [Tilde F] where
  essentially_undec : ∀ 𝓣 : S, 𝓢 ⪯ 𝓣 → Incomplete 𝓣 → Undecidable 𝓣

variable {𝓢}

lemma decidable_of_incomplete : Inconsistent 𝓢 → Decidable 𝓢 :=
  fun h ↦ ⟨by rw [h.theory_eq]; exact ComputablePred.const _⟩

namespace EssentiallyUndecidable

variable [Tilde F]

lemma undecidable (𝓢 : S) [EssentiallyUndecidable 𝓢] [Incomplete 𝓢] : Undecidable 𝓢 :=
  essentially_undec 𝓢 (WeakerThan.refl 𝓢) inferInstance

lemma of_weakerThan (𝓢 𝓣 : S) [EssentiallyUndecidable 𝓢] [𝓢 ⪯ 𝓣] :
    EssentiallyUndecidable 𝓣 where
  essentially_undec 𝓤 h₁ h₂ :=
    essentially_undec (𝓢 := 𝓢) 𝓤 (WeakerThan.trans (𝓣 := 𝓣) inferInstance h₁) h₂

end EssentiallyUndecidable

end

end FFL.Entailment

end

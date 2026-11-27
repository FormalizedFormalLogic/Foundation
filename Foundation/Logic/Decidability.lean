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

variable (P : S → Prop)

/-- Every consistent extension of `𝓢` satisfying `P` is undecidable.

- [Kur23, Definition 2.5]
-/
class EssentiallyUndecidable where
  essentially_undec : ∀ 𝓣 : S, 𝓢 ⪯ 𝓣 → Consistent 𝓣 → P 𝓣 → Undecidable 𝓣

omit [Primcodable F] in
/-- Every consistent extension of `𝓢` satisfying `P` is incomplete.

- [Kur23, Definition 2.5]
-/
class EssentiallyIncomplete [Tilde F] where
  essentially_incomplete : ∀ 𝓣 : S, 𝓢 ⪯ 𝓣 → Consistent 𝓣 → P 𝓣 → Incomplete 𝓣

variable {𝓢 P}

lemma decidable_of_inconsistent : Inconsistent 𝓢 → Decidable 𝓢 :=
  fun h ↦ ⟨by rw [h.theory_eq]; exact ComputablePred.const _⟩

namespace EssentiallyUndecidable

lemma undecidable (𝓢 : S) [EssentiallyUndecidable 𝓢 P] [Consistent 𝓢] (h : P 𝓢) :
    Undecidable 𝓢 :=
  essentially_undec 𝓢 (WeakerThan.refl 𝓢) inferInstance h

lemma of_weakerThan (𝓢 𝓣 : S) [EssentiallyUndecidable 𝓢 P] [𝓢 ⪯ 𝓣] :
    EssentiallyUndecidable 𝓣 P where
  essentially_undec 𝓤 h₁ :=
    essentially_undec (𝓢 := 𝓢) 𝓤 (WeakerThan.trans (𝓣 := 𝓣) inferInstance h₁)

end EssentiallyUndecidable

end

end FFL.Entailment

end

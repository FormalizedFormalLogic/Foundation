module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition
public import Foundation.Modal.Hilbert.Normal.Basic
public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Kripke.Intuitionistic
public import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

@[expose] public section
namespace LO


structure FirstOrder.Operation (L : FirstOrder.Language) where
  val : FirstOrder.Sentence L → FirstOrder.Sentence L

namespace FirstOrder.Operation

instance : CoeFun (Operation L) (fun _ ↦ FirstOrder.Sentence L → FirstOrder.Sentence L) := ⟨fun 𝓞 ↦ 𝓞.val⟩

end FirstOrder.Operation


namespace Modal

abbrev FirstOrderInterpretation (L : FirstOrder.Language) (α) := α → FirstOrder.Sentence L

namespace Formula

def interpretFO {L α} (𝓞 : FirstOrder.Operation L) (f : FirstOrderInterpretation L α) : Modal.Formula α → FirstOrder.Sentence L
  | .atom a => f a
  |       ⊥ => ⊥
  |   φ ➝ ψ => (φ.interpretFO 𝓞 f) ➝ (ψ.interpretFO 𝓞 f)
  |      □φ => 𝓞 (φ.interpretFO 𝓞 f)

end Formula

end Modal

end LO

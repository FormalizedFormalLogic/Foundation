module
import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Closure

attribute [instance] IsAsymm.isIrrefl

namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}

protected abbrev Frame.IsAsymmetric (F : Frame) := IsAsymm _ F.Rel

lemma Frame.asymm [F.IsAsymmetric] : ∀ {x y : F.World}, x ≺ y → ¬y ≺ x := by apply IsAsymm.asymm

instance [F.IsAsymmetric] : F.IsIrreflexive := ⟨by simp⟩

end Kripke

end LO.Modal

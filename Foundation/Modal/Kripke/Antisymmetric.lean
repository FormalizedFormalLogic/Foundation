import Foundation.Modal.Kripke.AxiomGeach


namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}


protected abbrev Frame.IsAntisymmetric (F : Frame) := IsAntisymm _ F.Rel

lemma Frame.antisymm [F.IsAntisymmetric] : ∀ {x y : F.World}, x ≺ y → y ≺ x → x = y := by apply IsAntisymm.antisymm

protected class Frame.IsPartialOrder (F : Frame) extends F.IsReflexive, F.IsTransitive, F.IsAntisymmetric

end Kripke

end LO.Modal

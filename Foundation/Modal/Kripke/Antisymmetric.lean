import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Closure


namespace LO.Modal

namespace Kripke

variable {F : Kripke.Frame}


protected abbrev Frame.IsAntisymmetric (F : Frame) := IsAntisymm _ F.Rel

lemma Frame.antisymm [F.IsAntisymmetric] : ∀ {x y : F.World}, x ≺ y → y ≺ x → x = y := by apply IsAntisymm.antisymm


protected abbrev Frame.IsPartialOrder (F : Frame) := IsPartialOrder _ F.Rel

instance [F.IsPartialOrder] : F.IsReflexive := by simp
instance [F.IsPartialOrder] : F.IsTransitive := by simp
instance [F.IsPartialOrder] : F.IsAntisymmetric := ⟨by apply Frame.antisymm⟩

end Kripke

end LO.Modal

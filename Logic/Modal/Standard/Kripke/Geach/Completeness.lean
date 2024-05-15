import Logic.Modal.Standard.Kripke.Completeness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α} [Inhabited α] [DecidableEq α]

instance [Λ.IsGeach] : Canonical Λ where
  definability := AxiomSet.IsGeach.definability _ _
  satisfy := by sorry;

instance [Λ.IsGeach] : Complete Λ 𝔽(Λ, MCT Λ) := inferInstance

instance : Complete (𝐒𝟒 : AxiomSet α) 𝔽((𝐒𝟒 : AxiomSet α), MCT (𝐒𝟒 : AxiomSet α)) := inferInstance

instance : Complete (𝐒𝟓 : AxiomSet α) 𝔽((𝐒𝟓 : AxiomSet α), MCT (𝐒𝟓 : AxiomSet α)) := inferInstance

end Kripke

end LO.Modal.Standard

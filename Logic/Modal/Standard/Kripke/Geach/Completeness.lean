import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α}

instance [Λ.IsGeach] : Complete Λ 𝔽(Λ, W) := by sorry

instance : Complete (𝐒𝟒 : AxiomSet α) 𝔽(𝐒𝟒, W) := inferInstance

instance : Complete (𝐒𝟓 : AxiomSet α) 𝔽(𝐒𝟓, W) := inferInstance

end Kripke

end LO.Modal.Standard

import Logic.Vorspiel.BinaryRelations
import Logic.Modal.Standard.Geach
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.Modal.Standard

namespace Kripke

variable {W α : Type*}
variable {Λ : AxiomSet α}

instance [Λ.IsGeach] {𝔽Λ : AxiomSetFrameClass W Λ} : Complete Λ 𝔽Λ := by sorry

instance : Complete (𝐒𝟒 : AxiomSet α) (𝔽Λ : AxiomSetFrameClass W 𝐒𝟒) := inferInstance

instance : Complete (𝐒𝟓 : AxiomSet α) (𝔽Λ : AxiomSetFrameClass W 𝐒𝟓) := inferInstance

end Kripke

end LO.Modal.Standard

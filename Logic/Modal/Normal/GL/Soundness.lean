import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.GL.Semantics

namespace LO.Modal.Normal

variable {α β} [Inhabited α] [Inhabited β] [Finite β]

theorem AxiomSet.GL.finiteConsistent : AxiomSet.Consistent (𝐆𝐋 : AxiomSet α) := AxiomSet.consistent β

end LO.Modal.Normal

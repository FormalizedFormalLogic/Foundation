module

public import Foundation.FirstOrder.SetTheory.Basic.Model
public import Foundation.FirstOrder.SetTheory.Z.Basic

@[expose] public section
/-! # Basic properties of model of Z set theory -/

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

section

variable [Nonempty V]

instance [V↓[ℒₛₑₜ] ⊧* 𝗭] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := inferInstance

instance : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := Tarski.Structure.Eq.models_eqAxiom' ℒₛₑₜ V

instance [V↓[ℒₛₑₜ] ⊧* 𝗭] : V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧 := models_of_subtheory (U := 𝗭) inferInstance

instance [V↓[ℒₛₑₜ] ⊧* 𝗭] : V↓[ℒₛₑₜ] ⊧* 𝗦𝗘𝗣 := models_of_subtheory (U := 𝗭) inferInstance

end

end FFL.FirstOrder.SetTheory

module

public import Foundation.FirstOrder.SetTheory.Basic.Model
public import Foundation.FirstOrder.SetTheory.ZF.Basic

@[expose] public section
/-! # Basic properties of model of ZFC set theory-/

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

section

variable [Nonempty V]

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := inferInstance

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧* 𝗕𝗦𝗧 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧* 𝗦𝗘𝗣 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧* 𝗭 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧* 𝗥𝗘𝗣𝗟 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)

instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)

instance : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := Tarski.Structure.Eq.models_eqAxiom' ℒₛₑₜ V

end

end FFL.FirstOrder.SetTheory

module

public import Foundation.FirstOrder.SetTheory.Basic.Model
public import Foundation.FirstOrder.SetTheory.BST.Basic

@[expose] public section
/-! # Basic properties of model of BST set theory -/

namespace FFL.FirstOrder.SetTheory

variable {V : Type*} [SetStructure V]

section

variable [Nonempty V]

instance : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := Tarski.Structure.Eq.models_eqAxiom' ℒₛₑₜ V

end

end FFL.FirstOrder.SetTheory

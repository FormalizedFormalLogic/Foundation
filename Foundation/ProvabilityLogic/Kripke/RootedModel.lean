module

public import Foundation.ProvabilityLogic.Kripke.Basic

/-!
# Rooted Kripke models
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

/-- A Kripke model with a root, from which every other world is accessible. -/
structure RootedModel (κ : Type*) [Nonempty κ] (α : Type*) extends Model κ α where
  root : κ
  root_rel : ∀ x, x ≠ root → toModel.Rel root x

end FFL.ProvabilityLogic.Kripke

end

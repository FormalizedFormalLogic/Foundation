module

public import Foundation.FirstOrder.SetTheory.Z
public import Foundation.FirstOrder.SetTheory.NaturalNumberRec

/-!
# Transitive closure in Zermelo set theory

-/

@[expose] public section

namespace FFL.FirstOrder.SetTheory

namespace TransitiveClosure

variable (V : Type*) [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] (x : V)

def aux : NaturalNumberRec.Blueprint 1 := {
    zero := “y x. y = x”,
    succ := “y z i x. !sUnion.dfn y z”
  }



end TransitiveClosure

end FFL.FirstOrder.SetTheory

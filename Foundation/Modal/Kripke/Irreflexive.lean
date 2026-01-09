module
import Foundation.Modal.Kripke.Antisymmetric

namespace LO.Modal.Kripke

namespace Frame

variable {F : Frame} {x y z : F.World}

protected abbrev IsIrreflexive (F : Frame) := IsIrrefl _ F

@[simp] lemma irrefl [F.IsIrreflexive] (x : F) : ¬x ≺ x := by apply IsIrrefl.irrefl;


class IsStrictPreorder (F : Frame) extends F.IsIrreflexive, F.IsTransitive

end Frame

end LO.Modal.Kripke

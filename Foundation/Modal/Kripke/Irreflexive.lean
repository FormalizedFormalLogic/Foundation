module

public import Foundation.Modal.Kripke.Antisymmetric

@[expose] public section

namespace LO.Modal.Kripke

namespace Frame

variable {F : Frame} {x y z : F.World}

protected abbrev IsIrreflexive (F : Frame) := Std.Irrefl F

@[simp] lemma irrefl [F.IsIrreflexive] (x : F) : ¬x ≺ x := by apply Std.Irrefl.irrefl;


class IsStrictPreorder (F : Frame) extends F.IsIrreflexive, F.IsTransitive

end Frame

end LO.Modal.Kripke
end

import Foundation.Modal.Kripke.Irreflexive

namespace LO.Modal.Kripke

namespace Frame

variable {F : Frame} {x y z : F.World}

abbrev IrreflRel := F.Rel.IrreflGen
infix:50 " ≺^≠ " => IrreflRel

abbrev IrreflGen (F : Frame) : Frame := ⟨F.World, (· ≺^≠ ·)⟩
postfix:95 "^≠" => IrreflGen

namespace IrreflGen

instance : Coe (F.World) (F^≠.World) := ⟨id⟩

instance [Finite F] : Finite (F^≠) := inferInstance
instance [F.IsFinite] : (F^≠).IsFinite := inferInstance

instance : (F^≠).IsIrreflexive := ⟨IsIrrefl.irrefl⟩

instance [F.IsIrreflexive] [F.IsTransitive] : (F^≠).IsTransitive := by simp

instance [F.IsAntisymmetric] : F^≠.IsAntisymmetric := ⟨by
  rintro x y ⟨_, Rxy⟩ ⟨_, Ryx⟩;
  exact F.antisymm Rxy Ryx;
⟩

end IrreflGen

end Frame

end LO.Modal.Kripke

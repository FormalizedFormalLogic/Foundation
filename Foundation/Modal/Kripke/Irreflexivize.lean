module

public import Foundation.Modal.Kripke.Root

@[expose] public section

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

instance : (F^≠).IsIrreflexive := ⟨Std.Irrefl.irrefl⟩

instance [F.IsAntisymmetric] [F.IsTransitive] : (F^≠).IsTransitive := inferInstance

instance [F.IsAntisymmetric] : F^≠.IsAntisymmetric := ⟨by
  rintro x y ⟨Rxy, _⟩ ⟨Ryx, _⟩;
  exact F.antisymm Rxy Ryx;
⟩

instance [F.IsPiecewiseStronglyConnected] : (F^≠).IsPiecewiseConnected := ⟨by
  rintro x y z ⟨Rxy, _⟩ ⟨Ryz, _⟩;
  suffices y ≠ z → F^≠.Rel y z ∨ F^≠.Rel z y by tauto;
  intro nyz;
  rcases F.ps_connected Rxy Ryz with (Ryz | Rzy) <;> tauto;
⟩

instance [F.IsStronglyConnected] : (F^≠).IsConnected := ⟨by
  rintro x y;
  rcases F.s_connected (x := x) (y := y) with (Rxy | Ryx) <;> tauto;
⟩

end IrreflGen

end Frame

end LO.Modal.Kripke
end

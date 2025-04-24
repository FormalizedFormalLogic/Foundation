import Foundation.Modal.Kripke.Preservation
import Foundation.Modal.Kripke.Rooted

namespace LO.Modal.Kripke

abbrev NatLTFrame : Kripke.Frame where
  World := ℕ
  Rel := (· < ·)

namespace NatLTFrame

instance : IsTrans _ NatLTFrame := by
  dsimp only [NatLTFrame];
  infer_instance;

abbrev min : NatLTFrame.World := 0

instance : Frame.IsRooted NatLTFrame NatLTFrame.min where
  root_generates := by
    intro x hx;
    apply Relation.TransGen.single;
    simp_all [Frame.Rel', NatLTFrame, NatLTFrame.min];
    omega;

end NatLTFrame


abbrev NatLEFrame : Kripke.Frame where
  World := ℕ
  Rel := (· ≤ ·)

namespace NatLEFrame

instance : IsTrans _ NatLEFrame := by
  dsimp only [NatLEFrame];
  infer_instance;

instance : IsRefl _ NatLEFrame := by
  dsimp only [NatLEFrame];
  infer_instance;

abbrev min : NatLEFrame.World := 0

instance : Frame.IsRooted NatLEFrame NatLEFrame.min where
  root_generates := by
    intro x _;
    apply Relation.TransGen.single;
    simp_all [Frame.Rel', NatLEFrame, NatLEFrame.min];

end NatLEFrame


abbrev FinLTFrame (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· < ·)

namespace FinLTFrame

variable {n : ℕ} [NeZero n]

instance : Finite (FinLTFrame n) := by
  dsimp only [FinLTFrame];
  infer_instance;

end FinLTFrame


abbrev FinLEFrame (n : ℕ) [NeZero n] : Kripke.Frame where
  World := Fin n
  Rel := (· ≤ ·)

namespace FinLEFrame

variable {n : ℕ} [NeZero n]

instance : Finite (FinLTFrame n) := by
  dsimp only [FinLTFrame];
  infer_instance;

instance : IsTrans _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

instance : IsRefl _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

instance : IsAntisymm _ (FinLEFrame n) := by
  dsimp only [FinLEFrame];
  infer_instance;

end FinLEFrame


end LO.Modal.Kripke

module
import Foundation.Modal.Kripke.Closure

namespace LO.Modal.Kripke

class Frame.IsTerminated (F : Frame) (t : F.World) : Prop where
  terminal_terminated : ∀ x ≠ t, x ≺^+ t

namespace Frame.IsTerminated

variable {F : Frame} {t : F.World} [F.IsTerminated t]

lemma direct_terminated_of_trans [F.IsTransitive] : ∀ x ≠ t, x ≺ t := by
  intro x hx;
  exact Rel.TransGen.unwrap $ IsTerminated.terminal_terminated x hx;

end Frame.IsTerminated

end LO.Modal.Kripke

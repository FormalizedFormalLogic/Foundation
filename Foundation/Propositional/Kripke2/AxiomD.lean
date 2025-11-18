import Foundation.Propositional.Kripke2.Basic
import Foundation.Vorspiel.HRel.Convergent
import Foundation.Vorspiel.HRel.Euclidean
import Foundation.Vorspiel.HRel.Coreflexive

namespace LO.Propositional

open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame}


namespace Frame

protected abbrev IsSerial (F : Kripke2.Frame) := _root_.IsSerial F.Rel
lemma serial [F.IsSerial] : ∀ x : F, ∃ y, x ≺ y := IsSerial.serial

protected class IsWeakSerial (F : Kripke2.Frame) where
  weak_serial : ∀ {x y : F}, x ≺ y → ∃ z, y ≺ z
export IsWeakSerial (weak_serial)

instance [F.IsSerial] : F.IsWeakSerial := ⟨by
  intro _ y _;
  obtain ⟨z, Ryz⟩ := F.serial y;
  use z;
⟩

end Frame


@[simp high, grind .]
lemma valid_axiomD_of_isWeakSerial [F.IsWeakSerial] : F ⊧ ∼∼⊤ := by
  intro V x y Rxy h;
  contrapose! h;
  apply Satisfies.not_def_neg.mpr;
  obtain ⟨z, Ryz⟩ := F.weak_serial Rxy;
  use z;
  constructor;
  . assumption;
  . exact Satisfies.def_top

lemma isWeakSerial_of_valid_axiomD (h : F ⊧ ∼∼⊤) : F.IsWeakSerial := by
  constructor;
  intro x;
  simpa [Satisfies] using @h (λ v a => True) x;

end Kripke2

end LO.Propositional

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

end Frame


@[simp high, grind .]
lemma valid_axiomSer_of_isSerial [F.IsSerial] : F ⊧ Axioms.Ser := by
  intro V x y Rxy h;
  contrapose! h;
  apply Satisfies.not_def_neg.mpr;
  obtain ⟨z, Ryz⟩ := F.serial y;
  use z;
  constructor;
  . assumption;
  . exact Satisfies.def_top

lemma isSerial_of_valid_axiomSer (h : F ⊧ Axioms.Ser) : F.IsSerial := by
  constructor;
  intro x;
  simpa [Satisfies] using @h (λ v a => True) F.root x F.rooted;

end Kripke2

end LO.Propositional

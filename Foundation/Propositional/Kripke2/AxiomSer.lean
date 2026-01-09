module
import Foundation.Propositional.Kripke2.Basic
import Foundation.Propositional.Kripke2.FTheory
import Foundation.Vorspiel.Rel.Convergent
import Foundation.Vorspiel.Rel.Euclidean
import Foundation.Vorspiel.Rel.Coreflexive

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

instance [Entailment.F L] [Entailment.HasAxiomSer L] [Entailment.Disjunctive L] : Frame.IsSerial (canonicalModel L).toFrame where
  serial := by
    rintro T;
    obtain ⟨U, _, _, _⟩ := FTheory.lindenbaum (T := T.toFTheory) $ show ∼⊤ ∉ T.theory by
      by_contra hC;
      apply T.no_bot;
      apply T.imp_closed ?_ hC;
      exact Entailment.Corsi.axiomSer;
    use U;

end Kripke2

end LO.Propositional

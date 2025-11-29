import Foundation.Propositional.FMT.Logic.VF

namespace LO.Propositional

open FMT

instance : Propositional.VF ⪱ Propositional.VF_D := by
  constructor;
  . apply Hilbert.VCorsi.weakerThan_of_subset_axioms;
    tauto;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D #0 #1 #2);
    constructor;
    . simp;
    . exact VF.unprovable_axiomD

end LO.Propositional

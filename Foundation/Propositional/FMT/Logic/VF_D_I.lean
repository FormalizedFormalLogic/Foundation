import Foundation.Propositional.FMT.Logic.VF_D
import Foundation.Propositional.FMT.Logic.VF_I

namespace LO.Propositional

open FMT

instance : Propositional.VF_D ⪯ Propositional.VF_D_I := by
  apply Hilbert.VCorsi.weakerThan_of_subset_axioms
  tauto;

instance : Propositional.VF_I ⪯ Propositional.VF_D_I := by
  apply Hilbert.VCorsi.weakerThan_of_subset_axioms
  tauto;

end LO.Propositional

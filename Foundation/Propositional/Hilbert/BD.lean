import Foundation.Propositional.Hilbert.Int
import Foundation.Propositional.BoundDepth


namespace LO.Propositional

namespace Hilbert

variable {n : ℕ+}

protected abbrev BD (n : ℕ+) : Hilbert ℕ := ⟨{Axioms.EFQ (.atom 0), Axioms.BoundDepth n}⟩
instance : (Hilbert.BD n).FiniteAxiomatizable where
instance : (Hilbert.BD n).HasEFQ where p := 0;

end Hilbert

end LO.Propositional

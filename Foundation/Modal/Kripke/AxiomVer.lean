import Foundation.Vorspiel.BinaryRelations
import Foundation.Modal.Kripke.Completeness

namespace LO.Modal

open Formula.Kripke

namespace Kripke

abbrev IsolatedFrameClass : FrameClass := { F | Isolated F }

instance : IsolatedFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => False⟩;
  tauto;

instance IsolatedFrameClass.DefinedByAxiomVer : IsolatedFrameClass.DefinedByFormula (Axioms.Ver (.atom 0)) :=
  FrameClass.definedByFormula_of_iff_mem_validate $ by
  intro F;
  constructor;
  . intro h V x y Rxy;
    have := h Rxy;
    contradiction;
  . intro h x y Rxy;
    have := h (λ _ _ => False) x y Rxy;
    simp [Formula.Kripke.Satisfies] at this;

end Kripke

end LO.Modal

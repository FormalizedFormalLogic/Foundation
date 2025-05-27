import Foundation.Modal.Kripke.Hilbert.K
import Foundation.Modal.Kripke.Hilbert.Triv
import Foundation.Modal.Kripke.Hilbert.Ver

namespace LO.Modal.Logic

instance : ProperSublogic Logic.Empty Logic.K := ⟨by
  constructor;
  . simp;
  . suffices ∃ φ, Hilbert.K ⊢! φ by tauto_set;
    use ⊤;
    simp;
⟩

instance : ProperSublogic Logic.Triv Logic.Univ := ⟨by
  constructor;
  . simp;
  . suffices ∃ φ, ¬Hilbert.Triv ⊢! φ by tauto_set;
    use ⊥;
    exact Hilbert.Triv.Kripke.consistent.not_bot;
⟩

instance : ProperSublogic Logic.Ver Logic.Univ := ⟨by
  constructor;
  . simp;
  . suffices ∃ φ, ¬Hilbert.Ver ⊢! φ by tauto_set;
    use ⊥;
    exact Hilbert.Ver.Kripke.consistent.not_bot;
⟩

instance {L : Logic} [L.Consistent] : ProperSublogic L Logic.Univ := ⟨by constructor <;> simp⟩

end LO.Modal.Logic

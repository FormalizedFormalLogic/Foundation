import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

protected abbrev Empty : Logic := ∅

protected abbrev Univ : Logic := Set.univ

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

end LO.Modal.Logic

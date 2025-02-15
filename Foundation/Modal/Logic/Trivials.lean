import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

protected abbrev Empty : Logic := ∅

protected abbrev Univ : Logic := Set.univ

theorem Empty_ssubset_K : Logic.Empty ⊂ Logic.K := by
  constructor;
  . simp;
  . suffices ∃ φ, Hilbert.K ⊢! φ by tauto_set;
    use ⊤;
    simp;

theorem Triv_ssubset_Univ : Logic.Triv ⊂ Logic.Univ := by
  constructor;
  . simp;
  . suffices ∃ φ, ¬Hilbert.Triv ⊢! φ by tauto_set;
    use ⊥;
    exact Hilbert.Triv.Kripke.consistent.not_bot;

theorem Ver_ssubset_Univ : Logic.Ver ⊂ Logic.Univ := by
  constructor;
  . simp;
  . suffices ∃ φ, ¬Hilbert.Ver ⊢! φ by tauto_set;
    use ⊥;
    exact Hilbert.Ver.Kripke.consistent.not_bot;

end LO.Modal.Logic

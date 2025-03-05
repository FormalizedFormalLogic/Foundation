import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem K4_ssubset_GL : Logic.K4 ⊂ Logic.GL := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.K4 ⊢! φ by simpa;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact Hilbert.K4.unprovable_AxiomL;
instance : ProperSublogic Logic.K4 Logic.GL := ⟨K4_ssubset_GL⟩

theorem GL_ssubset_Ver : Logic.GL ⊂ Logic.Ver := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬Hilbert.GL ⊢! φ by simpa;
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . by_contra hC;
      have := unnec! hC;
      have := Hilbert.GL.Kripke.consistent.not_bot;
      contradiction
instance : ProperSublogic Logic.GL Logic.Ver := ⟨GL_ssubset_Ver⟩

end LO.Modal.Logic

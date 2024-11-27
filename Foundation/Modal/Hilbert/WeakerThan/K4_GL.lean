import Foundation.Modal.System.GL
import Foundation.Modal.Hilbert.Maximal.Unprovability

namespace LO.Modal.Hilbert

open System
open Formula

lemma K4_weakerThan_GL [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.GL α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomFour!];

theorem K4_strictlyWeakerThan_GL : (Hilbert.K4 ℕ) <ₛ (Hilbert.GL ℕ) := by
  dsimp [StrictlyWeakerThan];
  constructor;
  . exact K4_weakerThan_GL;
  . apply System.not_weakerThan_iff.mpr;
    use (Axioms.L (atom 0));
    constructor;
    . exact axiomL!;
    . exact K4.unprovable_AxiomL;

end LO.Modal.Hilbert

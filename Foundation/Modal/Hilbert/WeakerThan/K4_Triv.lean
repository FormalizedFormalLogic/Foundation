import Foundation.Modal.Hilbert.Systems

namespace LO.Modal.Hilbert

open System

lemma K4_weakerThan_Triv [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.Triv α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomTc!];

end LO.Modal.Hilbert

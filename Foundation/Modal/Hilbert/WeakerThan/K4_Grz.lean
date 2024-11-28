import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.Grz

namespace LO.Modal.Hilbert

open System

lemma K4_weakerThan_Grz [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomFour!];

end LO.Modal.Hilbert

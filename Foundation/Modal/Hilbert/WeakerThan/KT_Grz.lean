import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.Grz

namespace LO.Modal.Hilbert

open System
open Formula (atom)

lemma KT_weakerThan_Grz [DecidableEq α] : (Hilbert.KT α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomT!];

end LO.Modal.Hilbert

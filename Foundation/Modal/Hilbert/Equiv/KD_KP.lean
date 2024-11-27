import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.KD
import Foundation.Modal.System.KP

namespace LO.Modal.Hilbert

open System

lemma KD_weakerThan_KP [DecidableEq α] : (Hilbert.KD α) ≤ₛ (Hilbert.KP α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomD!];

lemma KP_weakerThan_KD [DecidableEq α] : (Hilbert.KP α) ≤ₛ (Hilbert.KD α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomP!];

theorem KD_equiv_KP [DecidableEq α] : (Hilbert.KD α) =ₛ (Hilbert.KP α) := Equiv.antisymm_iff.mpr ⟨KD_weakerThan_KP, KP_weakerThan_KD⟩

end LO.Modal.Hilbert

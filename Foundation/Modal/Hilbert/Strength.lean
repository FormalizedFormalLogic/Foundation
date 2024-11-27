import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.System.Grz
import Foundation.Modal.System.GL
import Foundation.Modal.System.KD
import Foundation.Modal.System.KP

namespace LO.Modal

open System
open Formula (atom)

namespace Hilbert

lemma KT_weakerThan_S4 : (Hilbert.KT α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma KT_weakerThan_Grz [DecidableEq α] : (Hilbert.KT α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomT!];


lemma K4_weakerThan_S4 : (Hilbert.K4 α) ≤ₛ (Hilbert.S4 α) := normal_weakerThan_of_subset $ by intro; aesop;

lemma K4_weakerThan_Triv [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.Triv α) := normal_weakerThan_of_maxm $ by
  rintro φ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomTc!];

lemma K4_weakerThan_GL [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.GL α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomFour!];

lemma K4_weakerThan_Grz [DecidableEq α] : (Hilbert.K4 α) ≤ₛ (Hilbert.Grz α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) <;> simp only [axiomK!, axiomFour!];


lemma KD_weakerThan_KP [DecidableEq α] : (Hilbert.KD α) ≤ₛ (Hilbert.KP α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomD!];

lemma KP_weakerThan_KD [DecidableEq α] : (Hilbert.KP α) ≤ₛ (Hilbert.KD α) := normal_weakerThan_of_maxm $ by
  rintro _ (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;> simp only [axiomK!, axiomP!];

lemma KD_equiv_KP [DecidableEq α] : (Hilbert.KD α) =ₛ (Hilbert.KP α) := Equiv.antisymm_iff.mpr ⟨KD_weakerThan_KP, KP_weakerThan_KD⟩


lemma GL_weakerThan_GLS : (Hilbert.GL α) ≤ₛ (Hilbert.GLS α) := by
  apply System.weakerThan_iff.mpr;
  intro φ h;
  exact Deduction.maxm! (by left; simpa);

end Hilbert

end LO.Modal

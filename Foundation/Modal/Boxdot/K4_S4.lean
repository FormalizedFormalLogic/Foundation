import Foundation.Modal.Boxdot.Preliminaries
import Foundation.Modal.Hilbert.Strength
import Foundation.Modal.System.S4

namespace LO.Modal

open System
open Formula
open Hilbert.Deduction

variable [DecidableEq α]
variable {φ : Formula α}

lemma boxdotTranslatedK4_of_S4 : (Hilbert.S4 α) ⊢! φ → (Hilbert.K4 α) ⊢! φᵇ := boxdotTranslated $ by
  intro φ hp;
  simp at hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomT!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomFour!

lemma iff_boxdotTranslation_S4 : (Hilbert.S4 α) ⊢! φ ⭤ φᵇ := by
  induction φ using Formula.rec' with
  | hbox φ ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : (Hilbert.K4 α) ⊢! φᵇ) : (Hilbert.S4 α) ⊢! φ := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (weakerThan_iff.mp $ Hilbert.K4_weakerThan_S4) h

theorem iff_S4_boxdotTranslatedK4 : (Hilbert.K4 α) ⊢! φᵇ ↔ (Hilbert.S4 α) ⊢! φ:= by
  constructor;
  . apply S4_of_boxdotTranslatedK4;
  . apply boxdotTranslatedK4_of_S4;
instance : BoxdotProperty (Hilbert.K4 α) (Hilbert.S4 α) := ⟨iff_S4_boxdotTranslatedK4⟩

end LO.Modal

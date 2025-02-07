import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.System.S4
import Foundation.Modal.Hilbert2.WellKnown

namespace LO.Modal

open System
open Formula
open Hilbert.Deduction

namespace Hilbert

variable {φ : Formula ℕ}

lemma boxdotTranslatedK4_of_S4 : Hilbert.S4 ⊢! φ → Hilbert.K4 ⊢! φᵇ := boxdotTranslated $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_axiomT!;
  . exact boxdot_axiomFour!

lemma iff_boxdotTranslation_S4 : Hilbert.S4 ⊢! φ ⭤ φᵇ := by
  induction φ using Formula.rec' with
  | hbox φ ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : Hilbert.K4 ⊢! φᵇ) : Hilbert.S4 ⊢! φ := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ ((weakerThan_iff.mp $ Hilbert.K4_weakerThan_S4) h)

theorem iff_S4_boxdotTranslatedK4 : Hilbert.K4 ⊢! φᵇ ↔ Hilbert.S4 ⊢! φ:= ⟨S4_of_boxdotTranslatedK4, boxdotTranslatedK4_of_S4⟩

instance : BoxdotProperty Hilbert.K4 Hilbert.S4 := ⟨iff_S4_boxdotTranslatedK4⟩

end Hilbert

end LO.Modal

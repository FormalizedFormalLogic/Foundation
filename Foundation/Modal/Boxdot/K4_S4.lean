import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Entailment.S4
import Foundation.Modal.Logic.WellKnown

namespace LO.Modal

open Entailment
open Formula
open Hilbert.Deduction

namespace Hilbert

lemma provable_boxdotTranslated_K4_of_provable_S4 : Hilbert.S4 ⊢! φ → Hilbert.K4 ⊢! φᵇ := boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_axiomT!;
  . exact boxdot_axiomFour!

lemma provable_S4_iff_boxdotTranslated : Hilbert.S4 ⊢! φ ⭤ φᵇ := by
  induction φ using Formula.rec' with
  | hbox φ ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma provable_S4_of_provable_boxdotTranslated_K4 (h : Hilbert.K4 ⊢! φᵇ) : Hilbert.S4 ⊢! φ := by
  exact (and₂'! provable_S4_iff_boxdotTranslated) ⨀ ((weakerThan_iff.mp $ Hilbert.K4_weakerThan_S4) h)

theorem iff_boxdotTranslatedK4_S4 : Hilbert.K4 ⊢! φᵇ ↔ Hilbert.S4 ⊢! φ:= ⟨
  provable_S4_of_provable_boxdotTranslated_K4,
  provable_boxdotTranslated_K4_of_provable_S4
⟩

end Hilbert


instance : BoxdotProperty Logic.K4 Logic.S4 := ⟨Hilbert.iff_boxdotTranslatedK4_S4⟩


end LO.Modal

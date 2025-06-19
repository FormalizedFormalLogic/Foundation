import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Entailment.S4
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula
open Hilbert.Deduction

namespace Logic

lemma provable_boxdotTranslated_K4_of_provable_S4 : φ ∈ Logic.S4 → φᵇ ∈ Logic.K4 := Hilbert.boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_axiomT!;
  . exact boxdot_axiomFour!

lemma provable_S4_iff_boxdotTranslated : Hilbert.S4 ⊢! φ ⭤ φᵇ := by
  induction φ with
  | hbox φ ihp => exact E!_trans (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact ECC!_of_E!_of_E! ihp ihq;
  | _ => exact E!_id;

lemma provable_S4_of_provable_boxdotTranslated_K4 (h : φᵇ ∈ Logic.K4) : φ ∈ Logic.S4 := by
  exact (K!_right provable_S4_iff_boxdotTranslated) ⨀ ((weakerThan_iff.mp $ Hilbert.K4_weakerThan_S4) h)

theorem iff_boxdotTranslatedK4_S4 : φᵇ ∈ Logic.K4 ↔ φ ∈ Logic.S4 := ⟨
  provable_S4_of_provable_boxdotTranslated_K4,
  provable_boxdotTranslated_K4_of_provable_S4
⟩

instance : BoxdotProperty Logic.K4 Logic.S4 := ⟨iff_boxdotTranslatedK4_S4⟩

end Logic




end LO.Modal

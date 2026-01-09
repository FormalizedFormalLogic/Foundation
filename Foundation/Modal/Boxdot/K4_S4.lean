module
import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Entailment.S4
import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Formula

lemma provable_boxdotTranslated_K4_of_provable_S4 : Modal.S4 ⊢ φ → Modal.K4 ⊢ φᵇ :=
  Hilbert.Normal.of_provable_boxdotTranslated_axiomInstances $ by
    intro φ hp;
    rcases (by simpa [Axiom.instances] using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact boxdot_axiomK!;
    . exact boxdot_axiomT!;
    . exact boxdot_axiomFour!

lemma provable_S4_iff_boxdotTranslated : Modal.S4 ⊢ φ ⭤ φᵇ := by
  induction φ with
  | hbox φ ihp => exact E!_trans (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact ECC!_of_E!_of_E! ihp ihq;
  | _ => exact E!_id;

lemma provable_S4_of_provable_boxdotTranslated_K4 (h : Modal.K4 ⊢ φᵇ) : Modal.S4 ⊢ φ := by
  exact (K!_right provable_S4_iff_boxdotTranslated) ⨀ (WeakerThan.pbl h);

theorem iff_boxdotTranslatedK4_S4 : Modal.K4 ⊢ φᵇ ↔ Modal.S4 ⊢ φ := ⟨
  provable_S4_of_provable_boxdotTranslated_K4,
  provable_boxdotTranslated_K4_of_provable_S4
⟩

end LO.Modal

import Foundation.IntProp.Kripke.Completeness
import Foundation.Modal.Kripke.Geach
import Foundation.Modal.ModalCompanion.Basic

namespace LO.Modal

open LO.Kripke
open Modal.Kripke

variable {α : Type u} [DecidableEq α] [Inhabited α] [Encodable α]

variable {iΛ : IntProp.Hilbert α} {mΛ : Modal.Hilbert α}
variable {p q r : IntProp.Formula α}

lemma provable_S4_of_provable_efq : (𝐒𝟒 ⊢! pᵍ) → (𝐈𝐧𝐭 ⊢! p) := by
  contrapose;
  intro h;

  replace h := (not_imp_not.mpr $ IntProp.Kripke.Int_complete.complete) h;
  simp [IntProp.Formula.Kripke.ValidOnFrame, IntProp.Formula.Kripke.ValidOnModel] at h;
  obtain ⟨F, F_refl, F_trans, V, V_hered, w, hp⟩ := h;

  have h₁ : ∀ q x, IntProp.Formula.Kripke.Satisfies ⟨F, V⟩ x q ↔ (Modal.Formula.Kripke.Satisfies ⟨F, V⟩ x (qᵍ)) := by
    intro q x;
    induction q using IntProp.Formula.rec' generalizing x with
    | hatom a =>
      simp [GoedelTranslation];
      constructor;
      . intro _ _ h; exact V_hered h (by assumption);
      . intro h; exact h x (F_refl x);
    | hor p q ihp ihq =>
      simp only [GoedelTranslation];
      constructor;
      . rintro (hp | hq);
        . apply Formula.Kripke.Satisfies.or_def.mpr; left;
          exact ihp x |>.mp hp;
        . apply Formula.Kripke.Satisfies.or_def.mpr; right;
          exact ihq x |>.mp hq;
      . intro h;
        rcases Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
        . left; exact ihp x |>.mpr hp;
        . right; exact ihq x |>.mpr hq;
    | _ =>
      simp_all [IntProp.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];
  have : ¬(Modal.Formula.Kripke.Satisfies ⟨F, V⟩ w (pᵍ)) := (h₁ p w).not.mp hp;

  apply not_imp_not.mpr $ S4_sound_aux;
  simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
  use F;
  exact ⟨⟨F_refl, F_trans⟩, by use V, w⟩;

theorem provable_efq_iff_provable_S4 : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩
instance : ModalCompanion (α := α) 𝐈𝐧𝐭 𝐒𝟒 := ⟨provable_efq_iff_provable_S4⟩

end LO.Modal

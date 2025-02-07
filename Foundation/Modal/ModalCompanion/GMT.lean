import Foundation.IntProp.Kripke.Completeness
import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.ModalCompanion.Basic

namespace LO.Modal

open LO.IntProp
open Modal.Kripke

variable {iH : IntProp.Hilbert ℕ} {mH : Modal.Hilbert ℕ}
variable {φ ψ χ : IntProp.Formula ℕ}

lemma provable_S4_of_provable_efq : (Hilbert.S4) ⊢! φᵍ → (Hilbert.Int ℕ) ⊢! φ := by
  contrapose;
  intro h;

  replace h := (not_imp_not.mpr $ Hilbert.Int.Kripke.complete.complete) h;
  simp [IntProp.Formula.Kripke.ValidOnFrame, IntProp.Formula.Kripke.ValidOnModel] at h;
  obtain ⟨F, V, w, hp⟩ := h;

  have h₁ : ∀ ψ x, IntProp.Formula.Kripke.Satisfies ⟨F, V⟩ x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨F.World, F.Rel⟩, V⟩ x (ψᵍ)) := by
    intro ψ x;
    induction ψ using IntProp.Formula.rec' generalizing x with
    | hatom a =>
      unfold GoedelTranslation;
      constructor;
      . intro _ _ h;
        exact V.hereditary h $ by assumption;
      . intro h;
        exact h x (F.rel_refl' x);
    | hfalsum => simp [GoedelTranslation]; rfl;
    | hor φ ψ ihp ihq =>
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
    | _ => simp_all [GoedelTranslation, IntProp.Formula.Kripke.Satisfies, Modal.Formula.Kripke.Satisfies];

  apply not_imp_not.mpr $ Hilbert.S4.Kripke.sound.sound;
  apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model;
  use {World := F.World, Rel := F.Rel, Val := V};
  constructor;
  . constructor;
    . exact F.rel_refl';
    . exact F.rel_trans';
  . apply Formula.Kripke.ValidOnModel.not_of_exists_world;
    use w;
    exact (h₁ φ w).not.mp hp;

theorem iff_provable_Int_provable_S4 : (Hilbert.Int ℕ) ⊢! φ ↔ (Hilbert.S4) ⊢! φᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩

instance : ModalCompanion (Hilbert.Int ℕ) (Hilbert.S4) := ⟨iff_provable_Int_provable_S4⟩

end LO.Modal

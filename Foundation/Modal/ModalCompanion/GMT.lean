import Foundation.IntProp.Kripke.Hilbert.Int.Basic
import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.ModalCompanion.Basic

namespace LO.Modal

open LO.IntProp
open Modal.Kripke

variable {iH : IntProp.Hilbert ℕ} {mH : Modal.Hilbert ℕ}
variable {φ ψ χ : IntProp.Formula ℕ}

lemma provable_S4_of_provable_efq : (Hilbert.S4) ⊢! φᵍ → (Hilbert.Int) ⊢! φ := by
  contrapose;
  intro h;

  replace h := (not_imp_not.mpr $ Hilbert.Int.Kripke.complete.complete) h;
  obtain ⟨M, w, hM, hp⟩ := IntProp.Formula.Kripke.ValidOnFrameClass.exists_model_world_of_not h;

  have h₁ : ∀ ψ x, IntProp.Formula.Kripke.Satisfies M x ψ ↔ (Modal.Formula.Kripke.Satisfies ⟨⟨M.World, M.Rel⟩, M.Val⟩ x (ψᵍ)) := by
    intro ψ x;
    induction ψ using IntProp.Formula.rec' generalizing x with
    | hatom a =>
      unfold GoedelTranslation;
      constructor;
      . intro _ _ h;
        exact M.Val.hereditary h $ by assumption;
      . intro h;
        exact h x (M.rel_refl x);
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
  use {World := M.World, Rel := M.Rel, Val := M.Val};
  constructor;
  . constructor;
    . exact M.rel_refl;
    . exact M.rel_trans;
  . apply Formula.Kripke.ValidOnModel.not_of_exists_world;
    use w;
    exact (h₁ φ w).not.mp hp;

theorem iff_provable_Int_provable_S4 : (Hilbert.Int) ⊢! φ ↔ (Hilbert.S4) ⊢! φᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩

instance : ModalCompanion (Hilbert.Int) (Hilbert.S4) := ⟨iff_provable_Int_provable_S4⟩

end LO.Modal

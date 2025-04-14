import Foundation.ProvabilityLogic.Grz.Completeness

namespace LO.Modal

theorem Logic.S.no_bot : ⊥ ∉ Logic.S := by
  have hb : (⊥ : Formula ℕ) = ⊥ᵇ := by simp [Formula.BoxdotTranslation];
  rw [hb];
  apply ProvabilityLogic.iff_boxdot_GL_S.not.mp;
  rw [←hb];
  apply Logic.no_bot;

instance : Logic.S.Consistent := ⟨by
  apply Set.eq_univ_iff_forall.not.mpr;
  push_neg;
  use ⊥;
  exact Logic.S.no_bot;
⟩

end LO.Modal

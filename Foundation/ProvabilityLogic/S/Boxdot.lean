module

public import Foundation.ProvabilityLogic.S.Basic

/-!
# `GL` and `S` agree on boxdot translations
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke

namespace Logic.S

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem boxdotTranslate_iff_GL : 𝐒 ⊢ Aᵇ ↔ 𝐆𝐋 ⊢ Aᵇ := by
  constructor;
  · intro h;
    apply GL.iff_root_forces.mpr;
    intro _ _ M _;
    obtain ⟨i, hi⟩ := iff_eventually_forces_tail.mp h M;
    exact (RootedModel.toTail.forces_inr_boxdotTranslate_iff i).mp (hi i le_rfl);
  · exact of_GL;

end Logic.S

end FFL.ProvabilityLogic

end

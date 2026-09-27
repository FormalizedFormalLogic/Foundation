module

public import Foundation.ProvabilityLogic.S.Basic

/-!
# `GL` and `S` agree on boxdot translations
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Kripke

namespace Logic.S

variable {α : Type*} {A : Formula α}

theorem boxdotTranslate_iff_GL : 𝐒 ⊢ Aᵇ ↔ 𝐆𝐋 ⊢ Aᵇ :=
  ⟨fun h ↦ GL.iff_root_forces.mpr fun M _ ↦ by
    obtain ⟨i, hi⟩ := iff_eventually_forces_tail.mp h M;
    exact (RootedModel.toTail.forces_inr_boxdotTranslate_iff i).mp (hi i le_rfl), of_GL⟩

end Logic.S

end FFL.ProvabilityLogic

end

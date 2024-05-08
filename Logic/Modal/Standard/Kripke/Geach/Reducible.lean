import Logic.Modal.Standard.Kripke.Reducible
import Logic.Modal.Standard.Kripke.Geach.Definability
import Logic.Modal.Standard.Kripke.Geach.Completeness

namespace LO.Modal.Standard.Kripke

open Kripke

variable {W α : Type*} [DecidableEq α] [Inhabited α]
variable {Λ₁ Λ₂ : AxiomSet α}
variable (𝔽Λ₁ : AxiomSetFrameClass W Λ₁) (𝔽Λ₂ : AxiomSetFrameClass W Λ₂)
variable [Nonempty (AxiomSetFrameClass W Λ₁)] [hNE₂ : Inhabited (AxiomSetFrameClass W Λ₂)]
variable [hG₁ : Λ₁.IsGeach] [hG₂ : Λ₂.IsGeach]

lemma reducible_of_geach_defnability
  (hs : ∀ {F : Frame W α}, MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₂) F → MultiGeachConfluent (AxiomSet.IsGeach.taples Λ₁) F)
  : (Λ₁ ≤ₛ Λ₂) := by
  apply reducible_of_definability 𝔽Λ₁ 𝔽Λ₂ (AxiomSet.IsGeach.definability _ Λ₁) (AxiomSet.IsGeach.definability _ Λ₂);
  intro F hF;
  exact hs hF;

@[simp]
theorem reducible_KD_KT
  {𝔽Λ₁ : AxiomSetFrameClass W (𝐊𝐃 : AxiomSet α)}
  {𝔽Λ₂ : AxiomSetFrameClass W (𝐊𝐓 : AxiomSet α)}
  : (𝐊𝐃 : AxiomSet α) ≤ₛ 𝐊𝐓 := by
  apply reducible_of_geach_defnability 𝔽Λ₁ default;
  simp;
  apply serial_of_refl;

end LO.Modal.Standard.Kripke

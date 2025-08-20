import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke

abbrev FrameClass.irrefl : FrameClass := { F | F.IsIrreflexive }

theorem undefinable_irreflexive : ¬∃ φ, ∀ F, F ∈ FrameClass.irrefl ↔ (F ⊧ φ) := by
  by_contra hC
  obtain ⟨φ, h⟩ := hC

  let F₁ : Frame := ⟨Fin 2, (· ≠ ·)⟩
  let F₂ : Frame := ⟨Fin 1, (· = ·)⟩

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => 0,
    forth := by omega
    back := by
      intro x y h
      use 1 - x
      constructor
      . simpa
      . omega
  }
  have f_surjective : Function.Surjective f := by
    simp [Function.Surjective]
    aesop

  have : F₁.IsIrreflexive := { irrefl := by omega; }
  have : F₂.IsIrreflexive := by
    apply h F₂ |>.mpr
    apply validOnFrame_of_surjective_pseudoMorphism f f_surjective
    exact h F₁ |>.mp $ by simpa
  apply F₂.irrefl 0
  omega

end Kripke

end LO.Modal

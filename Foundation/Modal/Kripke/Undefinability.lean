import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke

abbrev FrameClass.irrefl : FrameClass := { F | Irreflexive F }

theorem undefinable_irreflexive : ¬∃ φ, FrameClass.irrefl.DefinedByFormula φ := by
  by_contra hC;
  obtain ⟨φ, ⟨h⟩⟩ := hC;
  replace h : ∀ F : Frame, Irreflexive F ↔ F ⊧ φ := by simpa using h;

  let F₁ : Frame := ⟨Fin 2, (· ≠ ·)⟩;
  let F₂ : Frame := ⟨Fin 1, (· = ·)⟩;

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => 0,
    forth := by omega;
    back := by
      intro x y h;
      use 1 - x;
      constructor;
      . simpa;
      . omega;
  };
  have f_surjective : Function.Surjective f := by
    simp [Function.Surjective];
    aesop;

  have : Irreflexive F₁ := by simp [Irreflexive, F₁];
  have : Irreflexive F₂ := by
    apply h F₂ |>.mpr;
    apply validOnFrame_of_surjective_pseudoMorphism f f_surjective;
    exact h F₁ |>.mp $ by simpa;
  have : ¬Irreflexive F₂ := by simp [Irreflexive, F₂];
  contradiction;

end Kripke

end LO.Modal

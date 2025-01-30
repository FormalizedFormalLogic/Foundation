import Foundation.Modal.Kripke.Preservation

namespace LO.Modal

namespace Kripke

abbrev IrreflexiveFrameClass : FrameClass := { F | Irreflexive F }

theorem undefinable_irreflexive : ¬∃ Ax : Theory ℕ, IrreflexiveFrameClass.DefinedBy Ax := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame := { World := Fin 2, Rel := (· ≠ ·) };
  let F₂ : Frame := { World := Fin 1, Rel := (· = ·) };

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => 0,
    forth := by aesop;
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
    apply theory_ValidOnFrame_of_surjective_pseudoMorphism f f_surjective;
    exact h F₁ |>.mp $ by simpa;
  have : ¬Irreflexive F₂ := by simp [Irreflexive, F₂];
  contradiction;

end Kripke

end LO.Modal

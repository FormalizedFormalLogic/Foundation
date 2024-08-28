import Logic.Modal.Standard.Kripke.Semantics
import Logic.Logic.Kripke.Preservation

namespace LO.Modal.Standard

open LO.Kripke

variable {α}

namespace Kripke

section ModalEquivalent


def ModalEquivalent {M₁ M₂ : Kripke.Model α} (w₁ : M₁.World) (w₂ : M₂.World) : Prop := ∀ {p}, w₁ ⊧ p ↔ w₂ ⊧ p
infix:50 " ↭ " => ModalEquivalent

open Formula

variable {M₁ M₂ : Kripke.Model α}
variable (Bi : M₁ ⇄ M₂)

lemma modal_equivalent_of_bisimilar (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro p;
  induction p using Formula.rec' generalizing x₁ x₂ with
  | hatom a => exact Bi.atomic bisx;
  | himp p q ihp ihq =>
    constructor;
    . intro hpq hp;
      exact ihq bisx |>.mp $ hpq $ ihp bisx |>.mpr hp;
    . intro hpq hp;
      exact ihq bisx |>.mpr $ hpq $ ihp bisx |>.mp hp;
  | hbox p ih =>
    constructor;
    . intro h y₂ rx₂y₂;
      obtain ⟨y₁, ⟨bisy, rx₁y₁⟩⟩ := Bi.back bisx rx₂y₂;
      exact ih bisy |>.mp (h _ rx₁y₁);
    . intro h y₁ rx₁y₁;
      obtain ⟨y₂, ⟨bisy, rx₂y₂⟩⟩ := Bi.forth bisx rx₁y₁;
      exact ih bisy |>.mpr (h _ rx₂y₂);
  | _ => simp_all;

end ModalEquivalent

open Formula

variable {F₁ F₂ : Kripke.Frame}
         {M₁ M₂ : Kripke.Model α}
         {p : Formula α}

lemma modal_equivalence_of_modal_morphism (f : M₁ →ₚ M₂) (w : M₁.World) : w ↭ (f w) := by
  apply modal_equivalent_of_bisimilar $ Model.PseudoEpimorphism.Bisimulation f;
  simp [Model.PseudoEpimorphism.Bisimulation];

lemma iff_formula_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁#α ⊧ p → F₂#α ⊧ p := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [Kripke.ValidOnFrame, Kripke.ValidOnModel] using h;
  simp [Kripke.ValidOnFrame, Kripke.ValidOnModel];

  obtain ⟨w₁, e⟩ := f_surjective w₂; subst e;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁;

  let M₁ : Model α := { Frame := F₁, Valuation := V₁ };
  let M₂ : Model α := { Frame := F₂, Valuation := V₂ };
  exact modal_equivalence_of_modal_morphism (M₁ := M₁) (M₂ := M₂) {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := by simp_all
  } w₁ |>.not.mpr h;

lemma iff_theory_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁#α ⊧* T → F₂#α ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact iff_formula_valid_on_frame_surjective_morphism f f_surjective (h hp);


abbrev IrreflexiveFrameClass : FrameClass := { F | Irreflexive F }

theorem undefinable_irreflexive : ¬∃ (Λ : DeductionParameter α), ∀ F, F ∈ 𝔽(Λ of α) ↔ F ∈ IrreflexiveFrameClass.{0} := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame := { World := PUnit ⊕ PUnit, Rel := (· ≠ ·) };
  have hIF₁ : Irreflexive F₁ := by simp [Irreflexive, Frame.Rel'];

  let F₂ : Frame := { World := PUnit, Rel := (· = ·) };

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => (),
    forth := by simp [Frame.Rel'],
    back := by simp_all [Frame.Rel'];
  };
  have f_surjective : Function.Surjective f := by simp [Function.Surjective];

  have : ¬Irreflexive F₂ := by simp [Irreflexive];
  have : Irreflexive F₂ := by simpa using
    (h F₂ |>.mp $ (iff_theory_valid_on_frame_surjective_morphism f f_surjective ) (h F₁ |>.mpr hIF₁));
  contradiction;

end Kripke

end LO.Modal.Standard

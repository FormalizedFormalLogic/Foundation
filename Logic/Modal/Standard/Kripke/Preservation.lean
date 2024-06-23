import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke


section Bisimulation


end Bisimulation


section Generation

class GeneratedSubframe (F F' : Kripke.Frame α) where
  subset : F'.World ⊆ F.World
  -- rel : ∀ x y : F'.World, F'.Rel' x y → F.Rel' x y
  closed : ∀ x y : F.World, x ≺ y → y.1 ∈ F'.World


end Generation


section Reduction

protected class Frame.reduction {F₁ F₂ : Kripke.Frame α} (f : F₁.World → F₂.World)  where
  forth : ∀ {w v : F₁.World}, w ≺ v → (f w) ≺ (f v)
  back : ∀ {w : F₁.World}, ∀ {v : F₂.World}, (f w) ≺ v → ∃ u, w ≺ u ∧ f u = v


protected class Model.reduction {M₁ M₂ : Kripke.Model α β} (f : M₁.World → M₂.World)  extends Frame.reduction f where
  atomic : ∀ {w : M₁.World}, ∀ {a}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a)


open Formula

variable {F₁ F₂ : Kripke.Frame α} {M₁ M₂ : Kripke.Model α β}

lemma iff_formula_satisfies_morphism (f : M₁.World → M₂.World) [Model.reduction f] {w : M₁.World} : (M₁, w) ⊧ p ↔ (M₂, (f w)) ⊧ p := by
  induction p using Formula.rec' generalizing w with
  | hatom p =>
    constructor;
    . apply Model.reduction.atomic |>.mp;
    . apply Model.reduction.atomic |>.mpr
  | hbox p ih =>
    constructor;
    . intro h w₂ hw₂;
      obtain ⟨w₁, ⟨hww₁, e⟩⟩ := Frame.reduction.back hw₂;
      have := ih.mp $ h hww₁;
      subst e;
      assumption;
    . intro h w' hww';
      exact ih.mpr $ h $ Frame.reduction.forth hww';
  | _ => simp_all;

lemma iff_formula_valid_on_frame_surjective_morphism (f : F₁ → F₂) [Frame.reduction f] (f_surjective : f.Surjective) : F₁ ⊧ p → F₂ ⊧ p := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [valid_on_KripkeFrame, valid_on_KripkeModel] using h;
  simp [valid_on_KripkeFrame, valid_on_KripkeModel];

  obtain ⟨w₁, e⟩ : ∃ w₁, f w₁ = w₂ := by apply f_surjective;
  subst e;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁;

  let M₁ : Model α := { Frame := F₁, Valuation := V₁ };
  let M₂ : Model α := { Frame := F₂, Valuation := V₂ };
  have : Model.reduction (M₁ := M₁) (M₂ := M₂) f := { atomic := by simp_all };
  exact iff_formula_satisfies_morphism (M₁ := M₁) (M₂ := M₂) f |>.not.mpr h;

lemma iff_theory_valid_on_frame_surjective_morphism (f : F₁ → F₂) [Frame.reduction f] (f_surjective : f.Surjective) : F₁ ⊧* T → F₂ ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact iff_formula_valid_on_frame_surjective_morphism f f_surjective (h hp);

end Reduction


end Kripke

end LO.Modal.Standard

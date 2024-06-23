import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke


section Bisimulation


end Bisimulation


section Generation

class GeneratedSubframe (F F' : Kripke.Frame α) where
  subset : F'.World ⊆ F.World
  rel : ∀ x y : F'.World, F'.Rel' x y ↔ F.Rel' ⟨x, (by aesop)⟩ ⟨y, (by aesop)⟩ -- MEMO: i.e. F.Rel' = F.Rel' ∪ (F.World × F.World)
  closed : ∀ x : F'.World, ∀ y : F.World, F.Rel' ⟨x.1, (by aesop)⟩ y → y.1 ∈ F'.World


end Generation


section Reduction

protected class Frame.reduction {F₁ F₂ : Kripke.Frame α} (f : F₁.World → F₂.World)  where
  forth : ∀ {w v : F₁.World}, w ≺ v → (f w) ≺ (f v)
  back : ∀ {w : F₁.World}, ∀ {v : F₂.World}, (f w) ≺ v → ∃ u, w ≺ u ∧ f u = v


protected class Model.reduction {M₁ M₂ : Kripke.Model α β} (f : M₁.World → M₂.World)  extends Frame.reduction f where
  atomic : ∀ {w : M₁.World}, ∀ {a}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a)


open Formula

variable {F₁ F₂ : Kripke.Frame' α β} {M₁ M₂ : Kripke.Model α β} {p : Formula β}

lemma iff_formula_satisfies_morphism (f : M₁.World → M₂.World) [Model.reduction f] {w : M₁.World}
  : (⟨M₁, w⟩ : (M : Model α β) × M.World) ⊧ p ↔ (⟨M₂, (f w)⟩ : (M : Model α β) × M.World) ⊧ p := by
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
  | _ => simp_all [kripke_satisfies];

lemma iff_formula_valid_on_frame_surjective_morphism (f : F₁.World → F₂.World) [Frame.reduction f] (f_surjective : f.Surjective) : F₁ ⊧ p → F₂ ⊧ p := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, hw₂, h⟩ := by simpa [valid_on_KripkeFrame, valid_on_KripkeModel] using h;
  simp [valid_on_KripkeFrame, valid_on_KripkeModel];

  obtain ⟨w₁, e⟩ := f_surjective ⟨w₂, hw₂⟩; rw [←e] at h;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁.1, w₁.2;

  let M₁ : Model α β := { Frame := F₁, Valuation := V₁ };
  let M₂ : Model α β := { Frame := F₂, Valuation := V₂ };
  have : Model.reduction (M₁ := M₁) (M₂ := M₂) f := { atomic := by simp_all };
  exact iff_formula_satisfies_morphism (M₁ := M₁) (M₂ := M₂) f |>.not.mpr h;

lemma iff_theory_valid_on_frame_surjective_morphism (f : F₁.World → F₂.World) [Frame.reduction f] (f_surjective : f.Surjective) : F₁ ⊧* T → F₂ ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact iff_formula_valid_on_frame_surjective_morphism f f_surjective (h hp);

abbrev IrreflexiveFrameClass : FrameClass := λ _ F => Irreflexive F.Rel'

theorem undefinable_irreflexive : ¬∃ (Ax : AxiomSet β), Ax.DefinesKripkeFrameClass IrreflexiveFrameClass := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  -- MEMO: `Rel := { (x, y) | x ≠ y }`で行けてほしいのだがなぜか通らない．
  let F₁ : Frame' (Fin 2) β := { World := {0, 1}, Rel := {(⟨0, by simp⟩, ⟨1, by simp⟩), (⟨1, by simp⟩, ⟨0, by simp⟩)} };
  have hIF₁ : Irreflexive F₁.Rel' := by simp [Irreflexive, Frame.Rel'];

  let F₂ : Frame' (Fin 2) β := { World := {0}, Rel := { (x, y) | x = y } };
  have hIF₂ : ¬Irreflexive F₂.Rel' := by simp [Irreflexive]; use ⟨0, (by simp)⟩; simp [Frame.Rel'];

  let f : F₁.World → F₂.World := λ _ => ⟨0, (by simp)⟩;
  have hSur : Function.Surjective f := by simp [Function.Surjective]; aesop;
  have : Frame.reduction f := {
    forth := by simp [Frame.Rel'];
    back := by
      intro x y Rxy; simp [Frame.Rel'] at Rxy;
      match x with
      | ⟨0, _⟩ => use ⟨1, (by simp)⟩; simp_all [Frame.Rel'];
      | ⟨1, _⟩ => use ⟨0, (by simp)⟩; simp_all [Frame.Rel'];
  };
  have : Irreflexive F₂.Rel' := h.mp $ iff_theory_valid_on_frame_surjective_morphism f hSur $ h.mpr hIF₁;
  contradiction;

end Reduction


end Kripke

end LO.Modal.Standard

import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open Kripke
open Formula Formula.Kripke

namespace Kripke

class Frame.pMorphism (F₁ : Frame W₁ α) (F₂ : Frame W₂ α) (f : W₁ → W₂) where
  forth : ∀ {w v : W₁}, F₁ w v → F₂ (f w) (f v)
  back : ∀ {w : W₁}, ∀ {v : W₂}, F₂ (f w) v → ∃ u, F₁ w u ∧ f u = v

class Model.pMorphism (M₁ : Model W₁ α) (M₂ : Model W₂ α) (f : W₁ → W₂) extends Frame.pMorphism M₁.frame M₂.frame f where
  atomic : ∀ {w : W₁}, ∀ {a : α}, (M₁.valuation w a) ↔ (M₂.valuation (f w) a)

end Kripke

variable {f : W₁ → W₂} {p : Formula α} {T : Theory α}
variable {M₁ : Model W₁ α} {M₂ : Model W₂ α}
variable {F₁ : Frame W₁ α} {F₂ : Frame W₂ α}

lemma Formula.Kripke.Satisfies.morphism (hMor : Model.pMorphism M₁ M₂ f) {w : W₁} : ((M₁, w) ⊧ p) ↔ ((M₂, (f w)) ⊧ p) := by
  induction p using Formula.rec' generalizing w with
  | hatom p =>
    constructor;
    . apply hMor.atomic |>.mp;
    . apply hMor.atomic |>.mpr
  | hbox p ih =>
    simp;
    constructor;
    . intro h w₂ hw₂;
      obtain ⟨w₁, ⟨hww₁, e⟩⟩ := hMor.back hw₂;
      have := ih.mp $ h w₁ hww₁;
      subst e;
      assumption;
    . intro h w' hww';
      exact ih.mpr $ h (f w') $ hMor.forth hww';
  | _ => simp_all;

lemma Formula.Kripke.ValidOnFrame.morphism (hSur : Function.Surjective f) (hMorF : Frame.pMorphism F₁ F₂ f) : (F₁ ⊧ p) → (F₂ ⊧ p) := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [ValidOnFrame, ValidOnModel] using h;
  let M₁ : Model W₁ α := {
    frame := F₁,
    valuation := λ w a => V₂ (f w) a
  }
  have hMor : Model.pMorphism M₁ ⟨F₂, V₂⟩ f := {
    forth := by intro w v hwv; apply hMorF.forth hwv,
    back := by intro w v h; apply hMorF.back h,
    atomic := by simp_all;
  }
  simp [ValidOnFrame, ValidOnModel];
  obtain ⟨w₁, e⟩ : ∃ w₁ : W₁, f w₁ = w₂ := by apply hSur;
  existsi M₁.valuation, w₁;
  subst e;
  exact Satisfies.morphism hMor |>.not.mpr h;

lemma Theory.Kripke.ValidOnFrame.morphism (hSur : Function.Surjective f) (hMorF : Frame.pMorphism F₁ F₂ f) : (F₁ ⊧* T) → (F₂ ⊧* T) := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact Formula.Kripke.ValidOnFrame.morphism hSur hMorF (h hp);

theorem Kripke.undefinability_irreflexive : ¬∃ (Ax : AxiomSet α), (∀ {W : Type} {F : Frame W α}, (Irreflexive F) ↔ F ⊧* Ax) := by
  let F₁ : Frame (Fin 2) α := λ w v => w ≠ v;
  have hIF₁ : Irreflexive F₁ := by simp [Irreflexive, F₁];

  let F₂ : Frame (Fin 1) α := λ w v => w = v;
  have hIF₂ : ¬Irreflexive F₂ := by simp [Irreflexive, F₂];

  let f : Fin 2 → Fin 1 := λ _ => 0;
  have hSur : Function.Surjective f := by trivial;
  have hMorF : Frame.pMorphism F₁ F₂ f := {
    forth := by intros; simp [F₂],
    back := by
      simp [F₂, F₁];
      intro w;
      match w with
      | 0 => use 1; trivial;
      | 1 => use 0; trivial;
  }

  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;
  have : F₁ ⊧* Ax := h.mp hIF₁;
  have : F₂ ⊧* Ax := Theory.Kripke.ValidOnFrame.morphism hSur hMorF this;
  have : Irreflexive F₂ := h.mpr this;
  contradiction;

end LO.Modal.Standard

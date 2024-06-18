import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open Kripke
open Formula

namespace Kripke

class Frame.pMorphism (F₁ : Frame) (F₂ : Frame) (f : F₁.World → F₂.World) where
  forth : ∀ {w v : F₁.World}, w ≺ v → (f w) ≺ (f v)
  back : ∀ {w : F₁.World}, ∀ {v : F₂.World}, (f w) ≺ v → ∃ u, w ≺ u ∧ f u = v

class Model.pMorphism (M₁ : Model α) (M₂ : Model α) (f : M₁.World → M₂.World) extends Frame.pMorphism M₁.Frame M₂.Frame f where
  atomic : ∀ {w : M₁.World}, ∀ {a : α}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a)

end Kripke

variable {M₁ : Model α} {M₂ : Model α}
         {F₁ : Frame' α} {F₂ : Frame' α}
         {f} {p : Formula α} {T : Theory α}

lemma Formula.kripke_satisfies.morphism (hMor : Model.pMorphism M₁ M₂ f) {w} : (w ⊧ p) ↔ ((f w) ⊧ p) := by
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

lemma Formula.valid_on_KripkeFrame.morphism (hSur : Function.Surjective f) (hMorF : Frame.pMorphism F₁ F₂ f) : (F₁ ⊧ p) → (F₂ ⊧ p) := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [valid_on_KripkeFrame, valid_on_KripkeModel] using h;

  simp [valid_on_KripkeFrame, valid_on_KripkeModel];
  obtain ⟨w₁, e⟩ : ∃ w₁, f w₁ = w₂ := by apply hSur;
  existsi λ w a => V₂ (f w) a, w₁;
  subst e;
  exact kripke_satisfies.morphism ({
    forth := by intro w v hwv; apply hMorF.forth hwv,
    back := by intro w v h; apply hMorF.back h,
    atomic := by simp_all;
  }) |>.not.mpr h;

lemma Theory.valid_on_KripkeFrame.morphism (hSur : Function.Surjective f) (hMorF : Frame.pMorphism F₁ F₂ f) : (F₁ ⊧* T) → (F₂ ⊧* T) := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact Formula.valid_on_KripkeFrame.morphism hSur hMorF (h hp);

-- TODO: Fix type `α`
theorem Kripke.undefinability_irreflexive : ¬∃ (Ax : AxiomSet α), (∀ {F : Frame'.{0} α}, (Irreflexive F.Rel) ↔ F ⊧* Ax) := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame' α := { World := Unit ⊕ Unit, Rel := λ w v => w ≠ v };
  have hIF₁ : Irreflexive F₁.Rel' := by exact f;

  let F₂ : Frame' α := { World := Unit, Rel := λ w v => w = v };
  have hIF₂ : ¬Irreflexive F₂.Rel' := by simp [Irreflexive]; existsi (); trivial;

  let f : F₁.World → F₂.World := λ _ => ();
  have hSur : Function.Surjective f := by simp [Function.Surjective];
  have hMorF : Frame.pMorphism F₁ F₂ f := {
    forth := by aesop;
    back := by
      simp [F₁, F₂];
      constructor;
      . intro a; right; exists (); intro; contradiction;
      . intro a; left; use (); intro; contradiction;
  }

  have : Irreflexive F₂.Rel := h.mpr $ Theory.valid_on_KripkeFrame.morphism hSur hMorF (h.mp hIF₁);
  contradiction;

end LO.Modal.Standard

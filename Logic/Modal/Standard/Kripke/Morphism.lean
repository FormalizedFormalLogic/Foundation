import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open Kripke
open Formula

namespace Kripke

class Frame.pMorphism (F₁ F₂ : Frame α) (f : F₁.World → F₂.World) where
  forth : ∀ {w v : F₁.World}, w ≺ v → (f w) ≺ (f v)
  back : ∀ {w : F₁.World}, ∀ {v : F₂.World}, (f w) ≺ v → ∃ u, w ≺ u ∧ f u = v

class Model.pMorphism (M₁ M₂ : Model α) (f : M₁.World → M₂.World) extends Frame.pMorphism M₁.Frame M₂.Frame f where
  atomic : ∀ {w : M₁.World}, ∀ {a : α}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a)

end Kripke

section

variable {p : Formula α} {T : Theory α}

lemma Formula.kripke_satisfies.morphism
  {M₁ M₂ : Model α} {f : M₁ → M₂} [morphism : Model.pMorphism M₁ M₂ f]
  {w : M₁.World} : w ⊧ p ↔ (f w) ⊧ p := by
  induction p using Formula.rec' generalizing w with
  | hatom p =>
    constructor;
    . apply morphism.atomic |>.mp;
    . apply morphism.atomic |>.mpr
  | hbox p ih =>
    simp;
    constructor;
    . intro h w₂ hw₂;
      obtain ⟨w₁, ⟨hww₁, e⟩⟩ := morphism.back hw₂;
      have := ih.mp $ h hww₁;
      subst e;
      assumption;
    . intro h w' hww';
      exact ih.mpr $ h $ morphism.forth hww';
  | _ => simp_all;

lemma Formula.valid_on_KripkeFrame.morphism
  {F₁ F₂ : Frame α} {f : F₁ → F₂} [morphism : Frame.pMorphism F₁ F₂ f]
  (hSur : f.Surjective)
  : F₁ ⊧ p → F₂ ⊧ p := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [valid_on_KripkeFrame, valid_on_KripkeModel] using h;

  simp [valid_on_KripkeFrame, valid_on_KripkeModel];
  obtain ⟨w₁, e⟩ : ∃ w₁, f w₁ = w₂ := by apply hSur;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁;
  subst e;

  have : Model.pMorphism { Frame := F₁, Valuation := V₁ } { Frame := F₂, Valuation := V₂ } f := {
    forth := morphism.forth,
    back := morphism.back,
    atomic := by simp_all
  };

  exact kripke_satisfies.morphism.not.mpr h;


lemma Theory.valid_on_KripkeFrame.morphism
  {F₁ F₂ : Frame α} {f : F₁ → F₂} [morphism : Frame.pMorphism F₁ F₂ f]
  (hSur : Function.Surjective f) : (F₁ ⊧* T) → (F₂ ⊧* T) := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact Formula.valid_on_KripkeFrame.morphism hSur (h hp);

end

-- TODO: Fix type `α`
theorem Kripke.undefinability_irreflexive : ¬∃ (Ax : AxiomSet α), (∀ {F : Frame.{0} α}, (Irreflexive F.Rel) ↔ F ⊧* Ax) := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame α := { World := Unit ⊕ Unit, Rel := λ w v => w ≠ v };
  have hIF₁ : Irreflexive F₁.Rel' := by simp [Irreflexive]; aesop

  let F₂ : Frame α := { World := Unit, Rel := λ w v => w = v };
  have hIF₂ : ¬Irreflexive F₂.Rel' := by simp [Irreflexive]; existsi (); trivial;

  let f : F₁.World → F₂.World := λ _ => ();
  have hSur : Function.Surjective f := by simp [Function.Surjective];
  have : Frame.pMorphism F₁ F₂ f := {
    forth := by aesop;
    back := by
      simp [F₁, F₂];
      constructor;
      . intro a; right; exists (); intro; contradiction;
      . intro a; left; use (); intro; contradiction;
  }

  have : Irreflexive F₂.Rel := h.mpr $ Theory.valid_on_KripkeFrame.morphism hSur (h.mp hIF₁);
  contradiction;

end LO.Modal.Standard

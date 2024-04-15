import Logic.Modal.Normal.Semantics

/-!
  # Morphisms

  ## Theorems
  - `undefinability_irreflexive`: In Kripke semantics, irreflexivity cannot be defined by some axioms.
-/

namespace LO.Modal.Normal

class Frame.pMorphism (F₁ : Frame α₁) (F₂ : Frame α₂) (f : α₁ → α₂) where
  forth : ∀ {w v : α₁}, F₁ w v → F₂ (f w) (f v)
  back : ∀ {w : α₁}, ∀ {v : α₂}, F₂ (f w) v → ∃ u : α₁, F₁ w u ∧ f u = v

class Model.pMorphism (M₁ : Model α₁ β) (M₂ : Model α₂ β) (f : α₁ → α₂) extends Frame.pMorphism M₁.frame M₂.frame f where
  atomic : ∀ {w : α₁}, ∀ {p : β}, (M₁.val w p) ↔ (M₂.val (f w) p)

variable {α₁ α₂ : Type} {β : Type} {f : α₁ → α₂}

lemma Formula.Satisfies.morphism
  {M₁ : Model α₁ β} {M₂ : Model α₂ β} (hMor : Model.pMorphism M₁ M₂ f)
  {w : α₁} {p : Formula β} : (w ⊩ᴹ[M₁] p) ↔ ((f w) ⊩ᴹ[M₂] p) := by
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

lemma Formula.Frames.morphism
  {F₁ : Frame α₁} {F₂ : Frame α₂}
  (hSur : Function.Surjective f)
  (hMorF : Frame.pMorphism F₁ F₂ f)
  {p : Formula β} : (⊧ᴹ[F₁] p) → (⊧ᴹ[F₂] p) := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [Formula.Frames, Formula.Models] using h;
  let M₁ : Model α₁ β := {
    frame := F₁,
    val := λ w a => V₂ (f w) a
  }
  have hMor : Model.pMorphism M₁ ⟨F₂, V₂⟩ f := {
    forth := by intro w v hwv; apply hMorF.forth hwv,
    back := by intro w v h; apply hMorF.back h,
    atomic := by simp_all;
  }
  simp [Formula.Frames, Formula.Models];
  obtain ⟨w₁, e⟩ : ∃ w₁ : α₁, f w₁ = w₂ := by apply hSur;
  existsi M₁.val, w₁;
  subst e;
  exact Formula.Satisfies.morphism hMor |>.not.mpr h;

lemma Theory.Frames.morphism
  {F₁ : Frame α₁} {F₂ : Frame α₂}
  (hSur : Function.Surjective f)
  (hMorF : Frame.pMorphism F₁ F₂ f)
  {Γ : Theory β} : (⊧ᴹ[F₁] Γ) → (⊧ᴹ[F₂] Γ) := by
  simp [Theory.Frames];
  intro h p hp;
  exact (Formula.Frames.morphism hSur hMorF) $ h p hp;

theorem undefinability_irreflexive : ¬∃ (Ax : AxiomSet β), (∀ {α : Type} {F : Frame α}, (Irreflexive F) ↔ ⊧ᴹ[F] Ax) := by
  let F₁ : Frame (Fin 2) := λ w v => w ≠ v;
  have hIF₁ : Irreflexive F₁ := by simp [Irreflexive, F₁];

  let F₂ : Frame (Fin 1) := λ w v => w = v;
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
  have : ⊧ᴹ[F₁] Ax := h.mp hIF₁;
  have : ⊧ᴹ[F₂] Ax := Theory.Frames.morphism hSur hMorF this;
  have : Irreflexive F₂ := h.mpr this;
  contradiction;

end LO.Modal.Normal

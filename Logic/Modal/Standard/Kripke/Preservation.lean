import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

variable {α}

namespace Kripke


section Bisimulation

structure Model.Bisimulation (M₁ M₂ : Kripke.Model α) where
  toRel : Rel M₁.World M₂.World
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : α} : toRel x₁ x₂ → ((M₁.Valuation x₁ a) ↔ (M₂.Valuation x₂ a))
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

notation M₁ " ⇄ " M₂ => Model.Bisimulation M₁ M₂

instance : CoeFun (Model.Bisimulation M₁ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨λ bi => bi.toRel⟩

end Bisimulation


section ModalEquivalent


def ModalEquivalent (M₁ M₂ : Kripke.Model α) (w₁ : M₁.World) (w₂ : M₂.World) : Prop := ∀ {p}, w₁ ⊧ p ↔ w₂ ⊧ p
notation:max "("  M₁ ", " w₁ ")" " ↭ " "("  M₂ ", " w₂ ")" => ModalEquivalent M₁ M₂ w₁ w₂

open Formula

variable {M₁ M₂ : Kripke.Model α}
variable (Bi : M₁ ⇄ M₂)

lemma modal_equivalent_of_bisimilar (bisx : Bi x₁ x₂) : (M₁, x₁) ↭ (M₂, x₂) := by
  intro p;
  induction p using Formula.rec' generalizing x₁ x₂ with
  | hatom a => exact Bi.atomic bisx;
  | hbox p ih =>
    constructor;
    . intro h y₂ rx₂y₂;
      obtain ⟨y₁, ⟨bisy, rx₁y₁⟩⟩ := Bi.back bisx rx₂y₂;
      exact ih bisy |>.mp (h rx₁y₁);
    . intro h y₁ rx₁y₁;
      obtain ⟨y₂, ⟨bisy, rx₂y₂⟩⟩ := Bi.forth bisx rx₁y₁;
      exact ih bisy |>.mpr (h rx₂y₂);
  | hand p q ihp ihq =>
    constructor;
    . rintro ⟨hp, hq⟩;
      exact ⟨ihp bisx |>.mp hp, ihq bisx |>.mp hq⟩;
    . rintro ⟨hp, hq⟩;
      exact ⟨ihp bisx |>.mpr hp, ihq bisx |>.mpr hq⟩;
  | hor p q ihp ihq =>
    constructor;
    . rintro (hp | hq);
      . left; exact ihp bisx |>.mp hp;
      . right; exact ihq bisx |>.mp hq;
    . rintro (hp | hq);
      . left; exact ihp bisx |>.mpr hp;
      . right; exact ihq bisx |>.mpr hq;
  | himp p q ihp ihq =>
    constructor;
    . intro hpq hp;
      exact ihq bisx |>.mp $ hpq $ ihp bisx |>.mpr hp;
    . intro hpq hp;
      exact ihq bisx |>.mpr $ hpq $ ihp bisx |>.mp hp;
  | hneg p ih =>
    constructor;
    . intro hnp hp;
      have := ih bisx |>.not.mp hnp;
      contradiction;
    . intro hnp hp;
      have := ih bisx |>.not.mpr hnp;
      contradiction;
  | _ => simp_all;

end ModalEquivalent


section PseudoEpimorphism

/-- As known as _p-morphism_. -/
structure Frame.PseudoEpimorphism (F₁ F₂ : Kripke.Frame) where
  toFun : F₁.World → F₂.World
  forth {x y : F₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : F₁.World} {v : F₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u

infix:80 " →ₚ " => Frame.PseudoEpimorphism

instance : CoeFun (Frame.PseudoEpimorphism F₁ F₂) (λ _ => F₁.World → F₂.World) := ⟨λ f => f.toFun⟩


structure Model.PseudoEpimorphism (M₁ M₂ : Kripke.Model α) extends M₁.Frame →ₚ M₂.Frame where
  atomic {w : M₁.World} {a} : (M₁.Valuation w a) ↔ (M₂.Valuation (toFun w) a)

infix:80 " →ₚ " => Model.PseudoEpimorphism

instance : CoeFun (Model.PseudoEpimorphism M₁ M₂) (λ _ => M₁.World → M₂.World) := ⟨λ f => f.toFun⟩

def Model.PseudoEpimorphism.mkAtomic
  {M₁ M₂ : Kripke.Model α}
  (f : M₁.Frame →ₚ M₂.Frame) (atomic : ∀ {w a}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a))
  : M₁ →ₚ M₂
  := {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := atomic,
  }

def Model.PseudoEpimorphism.Bisimulation {M₁ M₂ : Kripke.Model α} (f : M₁ →ₚ M₂) : M₁ ⇄ M₂ := {
  toRel := Function.graph f,
  atomic := by
    intro x₁ x₂ a e; subst e;
    constructor;
    . apply f.atomic.mp;
    . apply f.atomic.mpr;
  forth := by
    simp;
    intro x₁ y₁ rx₁y₁;
    exact f.forth rx₁y₁;
  back := by
    simp;
    intro x₁ x₂ y₂ e rx₂y₂; subst e;
    obtain ⟨y₁, _⟩ := f.back rx₂y₂;
    use y₁;
}

open Formula

variable {F₁ F₂ : Kripke.Frame}
         {M₁ M₂ : Kripke.Model α}
         {p : Formula α}

lemma modal_equivalence_of_modal_morphism (f : M₁ →ₚ M₂) {w : M₁.World} : (M₁, w) ↭ (M₂, f w) := by
  apply modal_equivalent_of_bisimilar $ Model.PseudoEpimorphism.Bisimulation f;
  simp [Model.PseudoEpimorphism.Bisimulation];

lemma iff_formula_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁# ⊧ p → F₂# ⊧ p := by
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
  } |>.not.mpr h;

lemma iff_theory_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁# ⊧* T → F₂# ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact iff_formula_valid_on_frame_surjective_morphism f f_surjective (h hp);

abbrev IrreflexiveFrameClass : FrameClass := { F | Irreflexive F }

theorem undefinable_irreflexive : ¬∃ (Ax : AxiomSet α), AxiomSet.DefinesKripkeFrameClass.{_, 0} Ax IrreflexiveFrameClass := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame := { World := Fin 2, default := 0, Rel := (· ≠ ·) };
  have hIF₁ : Irreflexive F₁ := by simp [Irreflexive, Frame.Rel'];

  let F₂ : Frame := { World := Fin 1, default := 0, Rel := (· = ·) };

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => 0,
    forth := by simp [Frame.Rel'],
    back := by
      simp;
      intro w;
      match w with
      | 0 => use 1; intro; contradiction;
      | 1 => use 0; intro; contradiction;
  };
  have f_surjective : Function.Surjective f := by simp [Function.Surjective]; aesop;

  have : ¬Irreflexive F₂ := by simp [Irreflexive];
  have : Irreflexive F₂ := h.mp $ iff_theory_valid_on_frame_surjective_morphism f f_surjective $ h.mpr hIF₁;
  contradiction;

end PseudoEpimorphism

end Kripke

end LO.Modal.Standard

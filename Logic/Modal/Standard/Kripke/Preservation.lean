import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke


section Bisimulation

end Bisimulation


section Generation

/-
class GeneratedSubframe (F F' : Kripke.Frame α) where
  subset : F'.World ⊆ F.World
  rel : ∀ {x y : F'.World}, x ≺ y ↔ F.Rel' ⟨x, (by aesop)⟩ ⟨y, (by aesop)⟩ -- MEMO: i.e. F.Rel' = F.Rel' ∪ (F.World × F.World)
  closed : ∀ {x : F'.World}, ∀ {y : F.World}, ⟨x.1, (by aesop)⟩ ≺ y → y.1 ∈ F'.World
-/

end Generation

section pMorphism

variable {α δ₁ δ₂}

structure Frame.pMorphism (F₁ : Kripke.Frame δ₁) (F₂ : Kripke.Frame δ₂) where
  toFun : F₁.World → F₂.World
  forth {x y : F₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : F₁.World} {v : F₂.World} : toFun w ≺ v → ∃ u, w ≺ u ∧ toFun u = v

infix:80 " →ₚ " => Frame.pMorphism

instance : CoeFun (Frame.pMorphism F₁ F₂) (λ _ => F₁.World → F₂.World) := ⟨λ f => f.toFun⟩


structure Model.pMorphism (M₁ : Kripke.Model δ₁ α) (M₂ : Kripke.Model δ₂ α) extends M₁.Frame →ₚ M₂.Frame where
  atomic {w : M₁.World} {a} : (M₁.Valuation w a) ↔ (M₂.Valuation (toFun w) a)

infix:80 " →ₚ " => Model.pMorphism

instance : CoeFun (Model.pMorphism M₁ M₂) (λ _ => M₁.World → M₂.World) := ⟨λ f => f.toFun⟩


open Formula

variable {F₁ : Kripke.Frame δ₁} {F₂ : Kripke.Frame δ₂}
         {M₁ : Kripke.Model δ₁ α} {M₂ : Kripke.Model δ₂ α}
         {p : Formula α}

lemma iff_formula_satisfies_morphism (f : M₁ →ₚ M₂) {w : M₁.World}
  : w ⊧ p ↔ (f w) ⊧ p := by
  induction p using Formula.rec' generalizing w with
  | hatom p =>
    constructor;
    . apply f.atomic |>.mp;
    . apply f.atomic |>.mpr
  | hbox p ih =>
    constructor;
    . intro h w₂ hw₂;
      obtain ⟨w₁, hww₁, e⟩ := f.back hw₂; subst e;
      exact ih.mp $ h hww₁;
    . intro h w' hww';
      exact ih.mpr $ h $ f.forth hww';
  | _ => simp_all [kripke_satisfies];

lemma iff_formula_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁[α] ⊧ p → F₂[α] ⊧ p := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := by simpa [valid_on_KripkeFrame, valid_on_KripkeModel] using h;
  simp [valid_on_KripkeFrame, valid_on_KripkeModel];

  obtain ⟨w₁, e⟩ := f_surjective w₂; subst e;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁;

  let M₁ : Model δ₁ α := { Frame := F₁, Valuation := V₁ };
  let M₂ : Model δ₂ α := { Frame := F₂, Valuation := V₂ };
  exact iff_formula_satisfies_morphism (M₁ := M₁) (M₂ := M₂) {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := by simp_all
  } |>.not.mpr h;

lemma iff_theory_valid_on_frame_surjective_morphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁[α] ⊧* T → F₂[α] ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h p hp;
  exact iff_formula_valid_on_frame_surjective_morphism f f_surjective (h hp);

abbrev IrreflexiveFrameClass : FrameClass := λ ⟨_, F⟩ => Irreflexive F

theorem undefinable_irreflexive : ¬∃ (Ax : AxiomSet α), AxiomSet.DefinesKripkeFrameClass.{_, 0} Ax IrreflexiveFrameClass := by
  by_contra hC;
  obtain ⟨Ax, h⟩ := hC;

  let F₁ : Frame (Fin 2) := { Rel := (· ≠ ·) };
  have hIF₁ : Irreflexive F₁ := by simp [Irreflexive, Frame.Rel'];

  let F₂ : Frame (Fin 1) := { Rel := (· = ·) };

  let f : F₁ →ₚ F₂ := {
    toFun := λ _ => 0,
    forth := by simp [Frame.Rel'],
    back := by
      simp;
      intro w;
      match w with
      | 0 => use 1; simp [Frame.Rel'];
      | 1 => use 0; simp [Frame.Rel'];
  };
  have f_surjective : Function.Surjective f := by simp [Function.Surjective]; aesop;

  have : ¬Irreflexive F₂ := by simp [Irreflexive];
  have : Irreflexive F₂ := h.mp $ iff_theory_valid_on_frame_surjective_morphism f f_surjective $ h.mpr hIF₁;
  contradiction;

end pMorphism

end Kripke

end LO.Modal.Standard

module

public import Foundation.Modal.Kripke.Logic.GL.Unnecessitation

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Kripke
open Formula.Kripke

namespace GL

namespace Kripke

abbrev mdpCounterexmpleFrame (F₁ F₂ : Frame) : Frame where
  World := Unit ⊕ F₁.World ⊕ F₂.World
  Rel := λ x y =>
    match x, y with
    | .inr (.inl x), .inr (.inl y) => x ≺ y -- F₁
    | .inr (.inr x), .inr (.inr y) => x ≺ y -- F₂
    | .inl _, .inl _ => False -- r ⊀ r
    | .inl _, _ => True -- r ≺ w₁ and r ≺ w₂ : w₁ ∈ F₁, w₂ ∈ F₂
    | _, _ => False

namespace mdpCounterexmpleFrame

variable {F₁ F₂ : Frame} -- [F₁.IsFiniteTree r₁] [F₂.IsFiniteTree r₂]

instance : Coe (F₁.World) (mdpCounterexmpleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (F₂.World) (mdpCounterexmpleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inr⟩

instance [F₁.IsAsymmetric] [F₂.IsAsymmetric]  : (mdpCounterexmpleFrame F₁ F₂).IsAsymmetric where
  asymm := by
    intro x y hxy;
    match x, y with
    | .inr (.inl x), .inr (.inl y)
    | .inr (.inr x), .inr (.inr y)
    | .inl x, .inr y => grind;
    | .inl x, .inl y => contradiction;

instance [F₁.IsTransitive] [F₂.IsTransitive] : (mdpCounterexmpleFrame F₁ F₂).IsTransitive where
  trans := by
    intro x y z hxy hyz;
    match x, y, z with
    | .inr (.inl x), .inr (.inl y), .inr (.inl z)
    | .inr (.inr x), .inr (.inr y), .inr (.inr z)
    | .inl _, .inr (.inr _), .inr (.inr _)
    | .inl _, .inr (.inl _), .inr (.inl _) => grind;

instance : (mdpCounterexmpleFrame F₁ F₂).IsPointRooted where
  default := ⟨.inl (), by grind⟩
  uniq {r} := by
    by_contra! hC;
    have := r.2 (.inl ()) (by grind);
    grind;

def pMorphism₁ (F₁ F₂) : F₁ →ₚ (mdpCounterexmpleFrame F₁ F₂) where
  toFun x := .inr (.inl x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by match y with | .inr (.inl y) => use y;

def pMorphism₂ (F₁ F₂) : F₂ →ₚ (mdpCounterexmpleFrame F₁ F₂) where
  toFun x := .inr (.inr x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by match y with | .inr (.inr y) => use y;

lemma through_original_root (r₁ : F₁.Root) (r₂ : F₂.Root) (x : (mdpCounterexmpleFrame F₁ F₂).World) (h : (mdpCounterexmpleFrame F₁ F₂).root ≺ x)
  : (x = r₁ ∨ (Sum.inr (Sum.inl r₁.1) ≺ x)) ∨ (x = r₂ ∨ (Sum.inr (Sum.inr r₂.1) ≺ x)) := by
  match x with
  | .inl x => grind;
  | .inr (.inl x) =>
    by_cases e : x = r₁;
    . subst e; left; tauto;
    . left; right;
      exact pMorphism₁ F₁ F₂ |>.forth $ (by grind)
  | .inr (.inr x) =>
    by_cases h : x = r₂;
    . subst h; right; tauto;
    . right; right;
      exact pMorphism₂ F₁ F₂ |>.forth $ (by grind);

end mdpCounterexmpleFrame


abbrev mdpCounterexmpleModel (M₁ M₂ : Model) : Model where
  toFrame := mdpCounterexmpleFrame (M₁.toFrame) (M₂.toFrame);
  Val := λ a x =>
    match x with
    | .inr (.inl x) => M₁.Val a x
    | .inr (.inr x) => M₂.Val a x
    | .inl _ => True

namespace mdpCounterexmpleModel

variable {M₁ M₂ : Model} -- {r₁ : M₁.World} {r₂ : M₂.World} [tree₁ : M₁.IsFiniteTree r₁] [tree₂ : M₂.IsFiniteTree r₂]

def pMorphism₁ (M₁ M₂) : M₁ →ₚ (mdpCounterexmpleModel M₁ M₂) :=
  Model.PseudoEpimorphism.ofAtomic (mdpCounterexmpleFrame.pMorphism₁ M₁.toFrame M₂.toFrame) $ by
  simp [mdpCounterexmpleFrame.pMorphism₁];

def pMorphism₂ (M₁ M₂) : M₂ →ₚ (mdpCounterexmpleModel M₁ M₂) :=
  Model.PseudoEpimorphism.ofAtomic (mdpCounterexmpleFrame.pMorphism₂ M₁.toFrame M₂.toFrame) $ by
  simp [mdpCounterexmpleFrame.pMorphism₂];

lemma modal_equivalence_original_world₁ {x : M₁.World} : ModalEquivalent (M₁ := M₁) (M₂ := (mdpCounterexmpleModel M₁ M₂)) x (↑x) := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence $ pMorphism₁ M₁ M₂;

lemma modal_equivalence_original_world₂ {x : M₂.World} : ModalEquivalent (M₁ := M₂) (M₂ := (mdpCounterexmpleModel M₁ M₂)) x (↑x) := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence $ pMorphism₂ M₁ M₂;

end mdpCounterexmpleModel

end Kripke


lemma MDP_Aux {X : Set _} (h : (□'X) *⊢[Modal.GL] □φ₁ ⋎ □φ₂) : (□'X) *⊢[Modal.GL] □φ₁ ∨ (□'X) *⊢[Modal.GL] □φ₂ := by
  obtain ⟨Δ, sΓ, hΓ⟩ := Context.provable_iff_boxed.mp h;

  have : Modal.GL ⊢ ⋀(□'Δ) ➝ (□φ₁ ⋎ □φ₂) := FiniteContext.provable_iff.mp hΓ;
  have : Modal.GL ⊢ □⋀Δ ➝ (□φ₁ ⋎ □φ₂) := C!_trans (by simp) this;
  generalize e : ⋀Δ = c at this;

  have : (Modal.GL ⊢ ⊡c ➝ φ₁) ∨ (Modal.GL ⊢ ⊡c ➝ φ₂) := by
    by_contra! hC;
    have ⟨h₁, h₂⟩ : (Modal.GL ⊬ ⊡c ➝ φ₁) ∧ (Modal.GL ⊬ ⊡c ➝ φ₂) := hC;

    obtain ⟨M₁, _, _, _, _, hM₁⟩ := GL.Kripke.iff_unprovable_exists_finite_rooted_model.mp h₁;
    obtain ⟨M₂, _, _, _, _, hM₂⟩ := GL.Kripke.iff_unprovable_exists_finite_rooted_model.mp h₂;

    let r₁ := M₁.root;
    let r₂ := M₂.root;
    let M₀ := Kripke.mdpCounterexmpleModel M₁ M₂;
    let r₀ : M₀.Root := M₀.root;

    replace hM₁ : Satisfies M₀ r₁ (⊡c ⋏ ∼φ₁) := Kripke.mdpCounterexmpleModel.modal_equivalence_original_world₁.mp (Formula.Kripke.Satisfies.not_imp.mp hM₁);
    replace hM₂ : Satisfies M₀ r₂ (⊡c ⋏ ∼φ₂) := Kripke.mdpCounterexmpleModel.modal_equivalence_original_world₂.mp (Formula.Kripke.Satisfies.not_imp.mp hM₂);

    have hc : Satisfies M₀ r₀ (□c) := by
      intro x Rrx;
      rcases Kripke.mdpCounterexmpleFrame.through_original_root r₁ r₂ x Rrx with ((rfl | Rrx) | (rfl | Rrx));
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).2 _ Rrx;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).2 _ Rrx;
    have hp₁ : ¬(Satisfies M₀ r₀ (□φ₁)) := by
      dsimp [Satisfies];
      push_neg;
      use (↑r₁);
      constructor;
      . tauto;
      . exact (Satisfies.and_def.mp hM₁).2;
    have hp₂ : ¬(Satisfies M₀ r₀ (□φ₂)) := by
      dsimp [Satisfies];
      push_neg;
      use (↑r₂);
      constructor;
      . tauto;
      . exact (Satisfies.and_def.mp hM₂).2;
    have : ¬(Satisfies M₀ r₀ (□φ₁ ⋎ □φ₂)) := by
      apply Satisfies.not_def.mpr;
      apply Satisfies.or_def.not.mpr;
      push_neg;
      exact ⟨hp₁, hp₂⟩;
    have : ¬(Satisfies M₀ r₀ (□c ➝ (□φ₁ ⋎ □φ₂))) := _root_.not_imp.mpr ⟨hc, this⟩;
    have : Modal.GL ⊬ □c ➝ □φ₁ ⋎ □φ₂ := GL.Kripke.iff_unprovable_exists_finite_rooted_model.mpr $ by
      use M₀, inferInstance, inferInstance, inferInstance, inferInstance;
      exact this;
    contradiction;

  rcases this with (h | h) <;> {
    subst e;
    have := imply_box_box_of_imply_boxdot_plain! h;
    have := C!_trans collect_box_conj! this;
    have := FiniteContext.provable_iff.mpr this;
    have := Context.provable_iff.mpr $ by use (□'Δ);
    tauto;
  };

theorem modal_disjunctive (h : Modal.GL ⊢ □φ₁ ⋎ □φ₂) : Modal.GL ⊢ φ₁ ∨ Modal.GL ⊢ φ₂ := by
  have : ∅ *⊢[Modal.GL] □φ₁ ∨ ∅ *⊢[Modal.GL] □φ₂ := by simpa [Set.LO.boxItr, Set.LO.preboxItr] using MDP_Aux (X := ∅) (φ₁ := φ₁) (φ₂ := φ₂) $ Context.of! h;
  rcases this with (h | h) <;> {
    have := unnec! $ Context.emptyPrf! h;
    tauto;
  }
instance : ModalDisjunctive Modal.GL := ⟨modal_disjunctive⟩

end GL

end LO.Modal
end

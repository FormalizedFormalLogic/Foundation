import Foundation.Modal.Kripke.Logic.GL.Unnecessitation

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment
open Kripke
open Formula.Kripke

namespace Hilbert.GL

namespace Kripke

abbrev mdpCounterexmpleFrame (F₁ F₂ : Frame) (r₁ r₂) [F₁.IsFiniteTree r₁] [F₂.IsFiniteTree r₂] : Frame where
  World := Unit ⊕ F₁.World ⊕ F₂.World
  Rel := λ x y =>
    match x, y with
    | .inr (.inl x), .inr (.inl y) => x ≺ y -- M₁
    | .inr (.inr x), .inr (.inr y) => x ≺ y -- M₂
    | .inl _, .inl _ => False -- r ⊀ r
    | .inl _, _ => True -- r ≺ w₁ and r ≺ w₂ : w₁ ∈ M₁, w₂ ∈ M₂
    | _, _ => False

namespace mdpCounterexmpleFrame

variable {F₁ F₂ : Frame} {r₁ : F₁.World} {r₂ : F₂.World} [F₁.IsFiniteTree r₁] [F₂.IsFiniteTree r₂]

instance : Coe (F₁.World) (mdpCounterexmpleFrame F₁ F₂ r₁ r₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (F₂.World) (mdpCounterexmpleFrame F₁ F₂ r₁ r₂).World := ⟨Sum.inr ∘ Sum.inr⟩

instance
  {F₁ F₂ : Frame} {r₁ : F₁.World} {r₂ : F₂.World} [tree₁ : F₁.IsFiniteTree r₁] [tree₂ : F₂.IsFiniteTree r₂]
  : (mdpCounterexmpleFrame F₁ F₂ r₁ r₂).IsFiniteTree (.inl ()) where
  root_generates := by
    intro x hx;
    match x with
    | .inl x => contradiction;
    | .inr _ =>
      apply Relation.TransGen.single;
      tauto;
  asymm := by
    intro x y hxy;
    match x, y with
    | .inr (.inl x), .inr (.inl y) => exact tree₁.asymm _ _ hxy;
    | .inr (.inr x), .inr (.inr y) => apply tree₂.asymm _ _ hxy;
    | .inl x, .inl y => contradiction;
    | .inl x, .inr y => simp;
  trans := by
    intro x y z hxy hyz;
    match x, y, z with
    | .inr (.inl x), .inr (.inl y), .inr (.inl z) => apply tree₁.trans _ _ _ hxy hyz;
    | .inr (.inr x), .inr (.inr y), .inr (.inr z) => apply tree₂.trans _ _ _ hxy hyz;
    | .inl _, .inr (.inr _), .inr (.inr _) => simp;
    | .inl _, .inr (.inl _), .inr (.inl _) => simp;

protected abbrev root : (mdpCounterexmpleFrame F₁ F₂ r₁ r₂).World := .inl ()

def pMorphism₁ : F₁ →ₚ (mdpCounterexmpleFrame F₁ F₂ r₁ r₂) where
  toFun x := .inr (.inl x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by match y with | .inr (.inl y) => use y;

def pMorphism₂ : F₂ →ₚ (mdpCounterexmpleFrame F₁ F₂ r₁ r₂) where
  toFun x := .inr (.inr x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by match y with | .inr (.inr y) => use y;

lemma through_original_root {x : (mdpCounterexmpleFrame F₁ F₂ r₁ r₂).World} (h : mdpCounterexmpleFrame.root ≺ x)
  : (x = r₁ ∨ (Sum.inr (Sum.inl r₁) ≺ x)) ∨ (x = r₂ ∨ (Sum.inr (Sum.inr r₂) ≺ x)) := by
  match x with
  | .inl x =>
    have := (@Frame.IsTree.rel_irreflexive (mdpCounterexmpleFrame F₁ F₂ r₁ r₂) mdpCounterexmpleFrame.root _);
    simp;
    simp at this;
    contradiction;
  | .inr (.inl x) =>
    by_cases e : x = r₁;
    . subst e; left; tauto;
    . left; right;
      exact pMorphism₁.forth $ Frame.IsRooted.direct_rooted_of_trans x e
  | .inr (.inr x) =>
    by_cases h : x = r₂;
    . subst h; right; tauto;
    . right; right;
      exact pMorphism₂.forth $ Frame.IsRooted.direct_rooted_of_trans x h

end mdpCounterexmpleFrame


abbrev mdpCounterexmpleModel (M₁ M₂ : Model) (r₁ r₂) [M₁.IsFiniteTree r₁] [M₂.IsFiniteTree r₂] : Model where
  toFrame := mdpCounterexmpleFrame (M₁.toFrame) (M₂.toFrame) r₁ r₂;
  Val := λ x a =>
    match x with
    | .inr (.inl x) => M₁.Val x a
    | .inr (.inr x) => M₂.Val x a
    | .inl _ => True

namespace mdpCounterexmpleModel

variable {M₁ M₂ : Model} {r₁ : M₁.World} {r₂ : M₂.World} [tree₁ : M₁.IsFiniteTree r₁] [tree₂ : M₂.IsFiniteTree r₂]

instance : Coe (M₁.World) (mdpCounterexmpleModel M₁ M₂ r₁ r₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (M₂.World) (mdpCounterexmpleModel M₁ M₂ r₁ r₂).World := ⟨Sum.inr ∘ Sum.inr⟩

abbrev root : (mdpCounterexmpleModel M₁ M₂ r₁ r₂).World := mdpCounterexmpleFrame.root (F₁ := M₁.toFrame) (F₂ := M₂.toFrame) (r₁ := r₁) (r₂ := r₂)

def pMorphism₁ : M₁ →ₚ (mdpCounterexmpleModel M₁ M₂ r₁ r₂) :=
  Model.PseudoEpimorphism.ofAtomic (mdpCounterexmpleFrame.pMorphism₁ (F₁ := M₁.toFrame) (F₂ := M₂.toFrame) (r₁ := r₁) (r₂ := r₂)) $ by
  simp [mdpCounterexmpleFrame.pMorphism₁];

def pMorphism₂ : M₂ →ₚ (mdpCounterexmpleModel M₁ M₂ r₁ r₂) :=
  Model.PseudoEpimorphism.ofAtomic (mdpCounterexmpleFrame.pMorphism₂ (F₁ := M₁.toFrame) (F₂ := M₂.toFrame) (r₁ := r₁) (r₂ := r₂)) $ by
  simp [mdpCounterexmpleFrame.pMorphism₂];

lemma modal_equivalence_original_world₁ {x : M₁.World} : ModalEquivalent (M₁ := M₁) (M₂ := (mdpCounterexmpleModel M₁ M₂ r₁ r₂)) x (↑x) := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence pMorphism₁;

lemma modal_equivalence_original_world₂ {x : M₂.World} : ModalEquivalent (M₁ := M₂) (M₂ := (mdpCounterexmpleModel M₁ M₂ r₁ r₂)) x (↑x) := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence pMorphism₂;

end mdpCounterexmpleModel

end Kripke


lemma MDP_Aux {X : Set _} (h : (X.box) *⊢[Hilbert.GL]! □φ₁ ⋎ □φ₂) : (X.box) *⊢[Hilbert.GL]! □φ₁ ∨ (X.box) *⊢[Hilbert.GL]! □φ₂ := by
  obtain ⟨Δ, sΓ, hΓ⟩ := Context.provable_iff_boxed.mp h;

  have : Hilbert.GL ⊢! ⋀Δ.box ➝ (□φ₁ ⋎ □φ₂) := FiniteContext.provable_iff.mp hΓ;
  have : Hilbert.GL ⊢! □⋀Δ ➝ (□φ₁ ⋎ □φ₂) := C!_trans (by simp) this;
  generalize e : ⋀Δ = c at this;

  have : (Hilbert.GL ⊢! ⊡c ➝ φ₁) ⋎ (Hilbert.GL ⊢! ⊡c ➝ φ₂) := by
    by_contra hC;
    have ⟨h₁, h₂⟩ : (Hilbert.GL ⊬ ⊡c ➝ φ₁) ∧ (Hilbert.GL ⊬ ⊡c ➝ φ₂) := not_or.mp hC;

    obtain ⟨M₁, r₁, _, hM₁⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₁;
    obtain ⟨M₂, r₂, _, hM₂⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₂;

    let M₀ := Kripke.mdpCounterexmpleModel M₁ M₂ r₁ r₂;
    let r₀ := Kripke.mdpCounterexmpleModel.root (M₁ := M₁) (M₂ := M₂) (r₁ := r₁) (r₂ := r₂)

    replace hM₁ : Satisfies M₀ ↑r₁ (⊡c ⋏ ∼φ₁) := Kripke.mdpCounterexmpleModel.modal_equivalence_original_world₁.mp (Formula.Kripke.Satisfies.not_imp.mp hM₁);
    replace hM₂ : Satisfies M₀ ↑r₂ (⊡c ⋏ ∼φ₂) := Kripke.mdpCounterexmpleModel.modal_equivalence_original_world₂.mp (Formula.Kripke.Satisfies.not_imp.mp hM₂);

    have hc : Satisfies M₀ r₀ (□c) := by
      intro x Rrx;
      rcases Kripke.mdpCounterexmpleFrame.through_original_root Rrx with ((rfl | Rrx) | (rfl | Rrx))
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).2 _ Rrx
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).2 _ Rrx
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
    have : Hilbert.GL ⊬ □c ➝ □φ₁ ⋎ □φ₂ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr $ by
      use M₀, r₀;
      constructor;
      . infer_instance;
      . exact this;
    contradiction;

  rcases this with (h | h) <;> {
    subst e;
    have := imply_box_box_of_imply_boxdot_plain! h;
    have := C!_trans collect_box_conj! this;
    have := FiniteContext.provable_iff.mpr this;
    have := Context.provable_iff.mpr $ by use Δ.box;
    tauto;
  };

theorem modal_disjunctive (h : Hilbert.GL ⊢! □φ₁ ⋎ □φ₂) : Hilbert.GL ⊢! φ₁ ∨ Hilbert.GL ⊢! φ₂ := by
  have : ∅ *⊢[Hilbert.GL]! □φ₁ ∨ ∅ *⊢[Hilbert.GL]! □φ₂ := by simpa using MDP_Aux (X := ∅) (φ₁ := φ₁) (φ₂ := φ₂) $ Context.of! h;
  rcases this with (h | h) <;> {
    have := unnec! $ Context.emptyPrf! h;
    tauto;
  }

end Hilbert.GL

end LO.Modal

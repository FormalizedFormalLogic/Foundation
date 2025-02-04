import Foundation.Modal.Kripke2.GL.Unnecessitation

namespace LO.Modal

open Kripke
open System
open Formula.Kripke

namespace Hilbert.GL

namespace Kripke

abbrev MDPCounterexampleFrame (F₁ F₂ : FiniteTransitiveTree) : FiniteTransitiveTree where
  World := Unit ⊕ F₁.World ⊕ F₂.World
  Rel := λ x y =>
    match x, y with
    | .inr (.inl x), .inr (.inl y) => x ≺ y -- M₁
    | .inr (.inr x), .inr (.inr y) => x ≺ y -- M₂
    | .inl _, .inl _ => False -- r ⊀ r
    | .inl _, _ => True -- r ≺ w₁ and r ≺ w₂ : w₁ ∈ M₁, w₂ ∈ M₂
    | _, _ => False
  root := .inl PUnit.unit
  root_rooted := by
    intro x hx;
    match x with
    | .inl x => contradiction;
    | .inr _ => simp [Frame.Rel'];
  rel_assymetric := by
    intro x y hxy;
    match x, y with
    | .inr (.inl x), .inr (.inl y) => apply F₁.rel_assymetric hxy;
    | .inr (.inr x), .inr (.inr y) => apply F₂.rel_assymetric hxy;
    | .inl x, .inl y => contradiction;
    | .inl x, .inr y => simp;
  rel_transitive := by
    intro x y z hxy hyz;
    match x, y, z with
    | .inr (.inl x), .inr (.inl y), .inr (.inl z) => apply F₁.rel_transitive hxy hyz;
    | .inr (.inr x), .inr (.inr y), .inr (.inr z) => apply F₂.rel_transitive hxy hyz;
    | .inl _, .inr (.inr _), .inr (.inr _) => simp;
    | .inl _, .inr (.inl _), .inr (.inl _) => simp;

namespace MDPCounterexampleFrame

variable {F₁ F₂ : FiniteTransitiveTree}

instance : Coe (F₁.World) (MDPCounterexampleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (F₂.World) (MDPCounterexampleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inr⟩

def p_morphism₁ : F₁.toFrame →ₚ (MDPCounterexampleFrame F₁ F₂).toFrame where
  toFun x := .inr (.inl x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by
    match y with
    | .inr (.inl y) => use y;

def p_morphism₂ : F₂.toFrame →ₚ (MDPCounterexampleFrame F₁ F₂).toFrame where
  toFun x := .inr (.inr x)
  forth := by
    intro x y hxy; exact hxy;
  back {x y} h := by
    match y with
    | .inr (.inr y) => use y;

lemma through_original_root {x : (MDPCounterexampleFrame F₁ F₂).World} (h : (MDPCounterexampleFrame F₁ F₂).root ≺ x)
  : (x = F₁.root ∨ (Sum.inr (Sum.inl F₁.root) ≺ x)) ∨ (x = F₂.root ∨ (Sum.inr (Sum.inr F₂.root) ≺ x)) := by
  match x with
  | .inl x =>
    have := (MDPCounterexampleFrame F₁ F₂).rel_irreflexive _ h;
    contradiction;
  | .inr (.inl x) =>
    by_cases h : x = F₁.root;
    . subst h; left; tauto;
    . left; right; exact p_morphism₁.forth $ F₁.root_rooted x h;
  | .inr (.inr x) =>
    by_cases h : x = F₂.root;
    . subst h; right; tauto;
    . right; right; exact p_morphism₂.forth $ F₂.root_rooted x h;

end MDPCounterexampleFrame

abbrev MDPCounterexampleModel (M₁ M₂ : FiniteTransitiveTreeModel) : FiniteTransitiveTreeModel where
  toFiniteTransitiveTree := MDPCounterexampleFrame M₁.toFiniteTransitiveTree M₂.toFiniteTransitiveTree
  Val := λ x a =>
    match x with
    | .inr (.inl x) => M₁.Val x a
    | .inr (.inr x) => M₂.Val x a
    | .inl _ => True

namespace MDPCounterexampleModel

variable {M₁ M₂ : FiniteTransitiveTreeModel}

instance : Coe (M₁.World) (MDPCounterexampleModel M₁ M₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (M₂.World) (MDPCounterexampleModel M₁ M₂).World := ⟨Sum.inr ∘ Sum.inr⟩

def p_morphism₁ : M₁.toModel →ₚ (MDPCounterexampleModel M₁ M₂).toModel := Model.PseudoEpimorphism.ofAtomic (MDPCounterexampleFrame.p_morphism₁) $ by
  simp [MDPCounterexampleFrame.p_morphism₁];

lemma modal_equivalence_original_world₁ {x : M₁.toModel.World} : ModalEquivalent (M₁ := M₁.toModel) (M₂ := (MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence p_morphism₁;

def p_morphism₂ : M₂.toModel →ₚ (MDPCounterexampleModel M₁ M₂).toModel := Model.PseudoEpimorphism.ofAtomic (MDPCounterexampleFrame.p_morphism₂) $ by
  simp [MDPCounterexampleFrame.p_morphism₂];

lemma modal_equivalence_original_world₂ {x : M₂.toModel.World} : ModalEquivalent (M₁ := M₂.toModel) (M₂ := (MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.Model.PseudoEpimorphism.modal_equivalence p_morphism₂;

end MDPCounterexampleModel

end Kripke


lemma MDP_Aux (h : (□''X) *⊢[Hilbert.GL]! □φ₁ ⋎ □φ₂) : (□''X) *⊢[Hilbert.GL]! □φ₁ ∨ (□''X) *⊢[Hilbert.GL]! □φ₂ := by
  obtain ⟨Δ, sΓ, hΓ⟩ := Context.provable_iff_boxed.mp h;

  have : Hilbert.GL ⊢! ⋀□'Δ ➝ (□φ₁ ⋎ □φ₂) := FiniteContext.provable_iff.mp hΓ;
  have : Hilbert.GL ⊢! □⋀Δ ➝ (□φ₁ ⋎ □φ₂) := imp_trans''! (by simp) this;
  generalize e : ⋀Δ = c at this;

  have : (Hilbert.GL ⊢! ⊡c ➝ φ₁) ⋎ (Hilbert.GL ⊢! ⊡c ➝ φ₂) := by
    by_contra hC;
    have ⟨h₁, h₂⟩ : (Hilbert.GL ⊬ ⊡c ➝ φ₁) ∧ (Hilbert.GL ⊬ ⊡c ➝ φ₂) := not_or.mp hC;

    obtain ⟨M₁, hM₁⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₁;
    obtain ⟨M₂, hM₂⟩ := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mp h₂;

    replace hM₁ := @Kripke.MDPCounterexampleModel.modal_equivalence_original_world₁ (M₁ := M₁) (M₂ := M₂) M₁.root (⊡c ⋏ ∼φ₁) |>.mp $ Formula.Kripke.Satisfies.not_imp.mp hM₁;
    replace hM₂ := @Kripke.MDPCounterexampleModel.modal_equivalence_original_world₂ (M₁ := M₁) (M₂ := M₂) M₂.root (⊡c ⋏ ∼φ₂) |>.mp $ Formula.Kripke.Satisfies.not_imp.mp hM₂;

    let M := Kripke.MDPCounterexampleModel M₁ M₂;

    have hc : Satisfies M.toModel M.root (□c) := by
      intro x Rrx;
      rcases Kripke.MDPCounterexampleFrame.through_original_root Rrx with ((rfl | Rrx) | (rfl | Rrx))
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).2 _ Rrx
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).2 _ Rrx
    have hp₁ : ¬(Satisfies M.toModel M.root (□φ₁)) := by
      dsimp [Satisfies]; push_neg;
      use .inr (.inl M₁.root);
      constructor;
      . apply M.root_rooted; simp;
      . exact (Satisfies.and_def.mp hM₁).2;
    have hp₂ : ¬(Satisfies M.toModel M.root (□φ₂)) := by
      dsimp [Satisfies]; push_neg;
      use .inr (.inr M₂.root);
      constructor;
      . apply M.root_rooted; simp;
      . exact (Satisfies.and_def.mp hM₂).2;
    have : ¬(Satisfies M.toModel M.root (□φ₁ ⋎ □φ₂)) := by
      apply Satisfies.not_def.mpr;
      apply Satisfies.or_def.not.mpr;
      push_neg;
      exact ⟨hp₁, hp₂⟩;
    have : ¬(Satisfies M.toModel M.root (□c ➝ (□φ₁ ⋎ □φ₂))) := _root_.not_imp.mpr ⟨hc, this⟩;
    have := Hilbert.GL.Kripke.iff_unprovable_exists_unsatisfies_FiniteTransitiveTree.mpr ⟨M, this⟩;
    contradiction;

  rcases this with (h | h) <;> {
    subst e;
    have := imply_box_box_of_imply_boxdot_plain! h;
    have := imp_trans''! collect_box_conj! this;
    have := FiniteContext.provable_iff.mpr this;
    have := Context.provable_iff.mpr $ by use □'Δ;
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

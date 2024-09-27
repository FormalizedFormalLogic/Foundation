import Logic.Modal.Kripke.GL.Tree

namespace LO.Modal

variable [Inhabited α] [DecidableEq α]

open LO.Kripke
open System
open Classical
open Formula.Kripke (Satisfies)
open Formula.Kripke.Satisfies
open Kripke Kripke.FiniteTransitiveTreeModel

namespace Kripke

abbrev GL_MDPCounterexampleFrame (F₁ F₂ : FiniteTransitiveTree) : FiniteTransitiveTree where
  World := PUnit ⊕ F₁.World ⊕ F₂.World
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
    simp at x y;
    match x, y with
    | .inr (.inl x), .inr (.inl y) => apply F₁.rel_assymetric hxy;
    | .inr (.inr x), .inr (.inr y) => apply F₂.rel_assymetric hxy;
    | .inl x, .inl y => contradiction;
    | .inl x, .inr y => simp;
  rel_transitive := by
    intro x y z hxy hyz;
    simp at x y z;
    match x, y, z with
    | .inr (.inl x), .inr (.inl y), .inr (.inl z) => apply F₁.rel_transitive hxy hyz;
    | .inr (.inr x), .inr (.inr y), .inr (.inr z) => apply F₂.rel_transitive hxy hyz;
    | .inl _, .inr (.inr _), .inr (.inr _) => simp;
    | .inl _, .inr (.inl _), .inr (.inl _) => simp;

namespace GL_MDPCounterexampleFrame

variable {F₁ F₂ : FiniteTransitiveTree}

instance : Coe (F₁.World) (GL_MDPCounterexampleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (F₂.World) (GL_MDPCounterexampleFrame F₁ F₂).World := ⟨Sum.inr ∘ Sum.inr⟩

def p_morphism₁ : F₁.toFrame →ₚ (GL_MDPCounterexampleFrame F₁ F₂).toFrame where
  toFun x := .inr (.inl x)
  forth := by intro x y hxy; exact hxy;
  back {x y} h := by
    simp [GL_MDPCounterexampleFrame] at y;
    match y with
    | .inr (.inl y) => use y;

def p_morphism₂ : F₂.toFrame →ₚ (GL_MDPCounterexampleFrame F₁ F₂).toFrame where
  toFun x := .inr (.inr x)
  forth := by
    intro x y hxy; exact hxy;
  back {x y} h := by
    simp [GL_MDPCounterexampleFrame] at y;
    match y with
    | .inr (.inr y) => use y;

lemma through_original_root {x : (GL_MDPCounterexampleFrame F₁ F₂).World} (h : (GL_MDPCounterexampleFrame F₁ F₂).root ≺ x)
  : (x = F₁.root ∨ (Sum.inr (Sum.inl F₁.root) ≺ x)) ∨ (x = F₂.root ∨ (Sum.inr (Sum.inr F₂.root) ≺ x)) := by
  match x with
  | .inl x =>
    simp [FiniteTransitiveTree.SimpleExtension.root_eq] at h;
    have := (GL_MDPCounterexampleFrame F₁ F₂).rel_irreflexive _ h;
    contradiction;
  | .inr (.inl x) =>
    by_cases h : x = F₁.root;
    . subst h; left; tauto;
    . left; right; exact p_morphism₁.forth $ F₁.root_rooted x h;
  | .inr (.inr x) =>
    by_cases h : x = F₂.root;
    . subst h; right; tauto;
    . right; right; exact p_morphism₂.forth $ F₂.root_rooted x h;

end GL_MDPCounterexampleFrame

abbrev GL_MDPCounterexampleModel (M₁ M₂ : FiniteTransitiveTreeModel α) : FiniteTransitiveTreeModel α where
  Tree := GL_MDPCounterexampleFrame M₁.Tree M₂.Tree
  Valuation := λ x a =>
    match x with
    | .inr (.inl x) => M₁.Valuation x a
    | .inr (.inr x) => M₂.Valuation x a
    | .inl _ => True

namespace GL_MDPCounterexampleModel

variable {M₁ M₂ : FiniteTransitiveTreeModel α}

instance : Coe (M₁.World) (GL_MDPCounterexampleModel M₁ M₂).World := ⟨Sum.inr ∘ Sum.inl⟩
instance : Coe (M₂.World) (GL_MDPCounterexampleModel M₁ M₂).World := ⟨Sum.inr ∘ Sum.inr⟩

def p_morphism₁ : M₁ →ₚ (GL_MDPCounterexampleModel M₁ M₂).toModel := Model.PseudoEpimorphism.mkAtomic (GL_MDPCounterexampleFrame.p_morphism₁) $ by
  simp [GL_MDPCounterexampleFrame.p_morphism₁];

lemma modal_equivalence_original_world₁ {x : M₁.toModel.World} : ModalEquivalent (M₁ := M₁) (M₂ := (GL_MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.modal_equivalence_of_modal_morphism p_morphism₁;

def p_morphism₂ : M₂ →ₚ (GL_MDPCounterexampleModel M₁ M₂).toModel := Model.PseudoEpimorphism.mkAtomic (GL_MDPCounterexampleFrame.p_morphism₂) $ by
  simp [GL_MDPCounterexampleFrame.p_morphism₂];

lemma modal_equivalence_original_world₂ {x : M₂.toModel.World} : ModalEquivalent (M₁ := M₂) (M₂ := (GL_MDPCounterexampleModel M₁ M₂).toModel) x x := by
  apply Kripke.modal_equivalence_of_modal_morphism p_morphism₂;

end GL_MDPCounterexampleModel

end Kripke

variable {X : Theory α} {p₁ p₂ : Formula α}

lemma GL_MDP_Aux (h : (□''X) *⊢[𝐆𝐋]! □p₁ ⋎ □p₂) : (□''X) *⊢[𝐆𝐋]! □p₁ ∨ (□''X) *⊢[𝐆𝐋]! □p₂ := by
  obtain ⟨Δ, sΓ, hΓ⟩ := Context.provable_iff_boxed.mp h;

  have : 𝐆𝐋 ⊢! ⋀□'Δ ➝ (□p₁ ⋎ □p₂) := FiniteContext.provable_iff.mp hΓ;
  have : 𝐆𝐋 ⊢! □⋀Δ ➝ (□p₁ ⋎ □p₂) := imp_trans''! (by simp) this;
  generalize e : ⋀Δ = c at this;

  have : (𝐆𝐋 ⊢! ⊡c ➝ p₁) ⋎ (𝐆𝐋 ⊢! ⊡c ➝ p₂) := by
    by_contra hC;
    have ⟨h₁, h₂⟩ : (𝐆𝐋 ⊬ ⊡c ➝ p₁) ∧ (𝐆𝐋 ⊬ ⊡c ➝ p₂) := not_or.mp hC;

    obtain ⟨M₁, hM₁⟩ := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h₁;
    obtain ⟨M₂, hM₂⟩ := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h₂;

    replace hM₁ := @GL_MDPCounterexampleModel.modal_equivalence_original_world₁ (M₁ := M₁) (M₂ := M₂) M₁.root (⊡c ⋏ ∼p₁) |>.mp $ Formula.Kripke.Satisfies.not_imp.mp hM₁;
    replace hM₂ := @GL_MDPCounterexampleModel.modal_equivalence_original_world₂ (M₁ := M₁) (M₂ := M₂) M₂.root (⊡c ⋏ ∼p₂) |>.mp $ Formula.Kripke.Satisfies.not_imp.mp hM₂;

    let M := GL_MDPCounterexampleModel M₁ M₂;

    have hc : Satisfies M.toModel M.root (□c) := by
      intro x Rrx;
      rcases GL_MDPCounterexampleFrame.through_original_root Rrx with ((rfl | Rrx) | (rfl | Rrx))
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₁).1).2 _ Rrx
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).1;
      . exact (Satisfies.and_def.mp $ (Satisfies.and_def.mp hM₂).1).2 _ Rrx
    have hp₁ : ¬(Satisfies M.toModel M.root (□p₁)) := by
      dsimp [Satisfies]; push_neg;
      use .inr (.inl M₁.root);
      constructor;
      . apply M.Tree.root_rooted; simp;
      . exact (Satisfies.and_def.mp hM₁).2;
    have hp₂ : ¬(Satisfies M.toModel M.root (□p₂)) := by
      dsimp [Satisfies]; push_neg;
      use .inr (.inr M₂.root);
      constructor;
      . apply M.Tree.root_rooted; simp;
      . exact (Satisfies.and_def.mp hM₂).2;
    have : ¬(Satisfies M.toModel M.root (□p₁ ⋎ □p₂)) := by
      apply Satisfies.not_def.mpr;
      apply Satisfies.or_def.not.mpr;
      push_neg;
      exact ⟨hp₁, hp₂⟩;
    have : ¬(Satisfies M.toModel M.root (□c ➝ (□p₁ ⋎ □p₂))) := _root_.not_imp.mpr ⟨hc, this⟩;
    have := iff_unprovable_GL_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr ⟨M, this⟩;
    contradiction;

  rcases this with (h | h) <;> {
    subst e;
    have := imply_box_box_of_imply_boxdot_plain! h;
    have := imp_trans''! collect_box_conj! this;
    have := FiniteContext.provable_iff.mpr this;
    have := Context.provable_iff.mpr $ by use □'Δ;
    tauto;
  };

theorem GL_MDP (h : 𝐆𝐋 ⊢! □p₁ ⋎ □p₂) : 𝐆𝐋 ⊢! p₁ ∨ 𝐆𝐋 ⊢! p₂ := by
  have := GL_MDP_Aux (X := ∅) (p₁ := p₁) (p₂ := p₂) $ Context.of! h;
  simp at this;
  rcases this with (h | h) <;> {
    have := unnec! $ Context.emptyPrf! h;
    tauto;
  }

instance : System.ModalDisjunctive (𝐆𝐋 : Hilbert α) := ⟨GL_MDP⟩

end LO.Modal

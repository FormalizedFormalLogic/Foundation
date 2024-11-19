import Mathlib.Data.Finite.Sum
import Foundation.Modal.Kripke.GL.Completeness
import Foundation.Modal.Kripke.Tree

namespace LO.Modal

variable {φ : Formula ℕ}

namespace Hilbert.GL.Kripke

open Classical
open Modal.Kripke
open Formula.Kripke

lemma valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass (h : TransitiveIrreflexiveFiniteFrameClass ⊧ φ) : ∀ T : FiniteTransitiveTree, T.toFrame ⊧ φ := by
  intro T;
  apply @h T.toFrame;
  use T.toFiniteFrame;
  refine ⟨⟨?_, ?_⟩, rfl⟩;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;

lemma satisfies_at_root_on_FiniteTransitiveTree (h : ∀ T : FiniteTransitiveTree, T.toFrame ⊧ φ) : ∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ := by
  intro M;
  exact h M.toFiniteTransitiveTree M.Val M.root;

lemma valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree
  : (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) → TransitiveIrreflexiveFiniteFrameClass ⊧ φ := by
  rintro H _ ⟨F, ⟨F_trans, F_irrefl⟩, rfl⟩ V r;
  let M : Kripke.Model := ⟨F.toFrame, V⟩;
  apply Model.PointGenerated.modal_equivalent_at_root F_trans r |>.mp;
  apply Model.TransitiveTreeUnravelling.modal_equivalence_at_root (M := (M↾r).toModel) (Frame.PointGenerated.rel_transitive F_trans) ⟨r, by tauto⟩ |>.mp;
  exact H ⟨(F.FiniteTransitiveTreeUnravelling F_trans F_irrefl r), (M.FiniteTransitiveTreeUnravelling r).Val⟩;

theorem provable_iff_satisfies_at_root_on_FiniteTransitiveTree : (Hilbert.GL ℕ) ⊢! φ ↔ (∀ M : FiniteTransitiveTreeModel, Satisfies M.toModel M.root φ) := by
  constructor;
  . intro h M;
    have : TransitiveIrreflexiveFiniteFrameClass ⊧ φ := Hilbert.GL.Kripke.finite_sound.sound h;
    have := valid_on_FiniteTransitiveTreeClass_of_valid_on_TransitiveIrreflexiveFrameClass this;
    exact satisfies_at_root_on_FiniteTransitiveTree this M;
  . intro h;
    apply Hilbert.GL.Kripke.complete.complete;
    intro F hF V;
    apply valid_on_TransitiveIrreflexiveFrameClass_of_satisfies_at_root_on_FiniteTransitiveTree h hF;

lemma unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree : (Hilbert.GL ℕ) ⊬ φ ↔ ∃ M : FiniteTransitiveTreeModel, ¬Satisfies M.toModel M.root φ := by
  apply Iff.not_left;
  push_neg;
  exact provable_iff_satisfies_at_root_on_FiniteTransitiveTree;

end Hilbert.GL.Kripke


namespace Kripke

def FiniteTransitiveTree.SimpleExtension (F : FiniteTransitiveTree) : Kripke.FiniteTransitiveTree where
  World := Unit ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inl _, .inr _ => True
    | _ , _ => False
  root := .inl ()
  root_rooted := by
    intro w;
    match w with
    | .inl _ => simp;
    | .inr x => simp [Frame.Rel]
  rel_assymetric := by
    intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    intro x y z hxy hyz;
    match x, y, z with
    | .inl _, .inr _, .inr _ => simp;
    | .inr x, .inr y, .inr z => exact F.rel_transitive hxy hyz;
postfix:max "↧" => FiniteTransitiveTree.SimpleExtension


namespace FiniteTransitiveTree.SimpleExtension

variable {T : FiniteTransitiveTree} {x y : T.World}

instance : Coe (T.World) (T↧.World) := ⟨Sum.inr⟩

@[simp] lemma root_not_original : (Sum.inr x) ≠ T↧.root := by simp [SimpleExtension]

lemma root_eq : (Sum.inl ()) = T↧.root := by simp [SimpleExtension];

lemma forth (h : x ≺ y) : T↧.Rel x y := by simpa [SimpleExtension];

def p_morphism : T.toFrame →ₚ (T↧.toFrame) where
  toFun x := x
  forth := forth
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', SimpleExtension] at h;
    | .inr y => use y; simpa using h;

lemma through_original_root {x : T↧.World} (h : T↧.root ≺ x) : x = T.root ∨ (Sum.inr T.root ≺ x) := by
  match x with
  | .inl x =>
    have := T↧.rel_irreflexive _ h;
    contradiction;
  | .inr x =>
    by_cases h : x = T.root;
    . subst h; left; tauto;
    . right; exact FiniteTransitiveTree.SimpleExtension.forth $ T.root_rooted x h;

end FiniteTransitiveTree.SimpleExtension


abbrev FiniteTransitiveTreeModel.SimpleExtension (M : FiniteTransitiveTreeModel) : Kripke.FiniteTransitiveTreeModel where
  toFiniteTransitiveTree := M.toFiniteTransitiveTree↧
  Val x a :=
    match x with
    | .inl _ => M.Val M.root a
    | .inr x => M.Val x a
postfix:max "↧" => FiniteTransitiveTreeModel.SimpleExtension


namespace FiniteTransitiveTreeModel.SimpleExtension

variable {M : FiniteTransitiveTreeModel}

instance : Coe (M.World) (M↧.World) := ⟨Sum.inr⟩

def p_morphism : M.toModel →ₚ (M↧.toModel) := Model.PseudoEpimorphism.mkAtomic (FiniteTransitiveTree.SimpleExtension.p_morphism) $ by
  simp [FiniteTransitiveTree.SimpleExtension.p_morphism];

lemma modal_equivalence_original_world {x : M.toModel.World} : ModalEquivalent (M₁ := M.toModel) (M₂ := (M↧).toModel) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence p_morphism;

end FiniteTransitiveTreeModel.SimpleExtension

end Kripke

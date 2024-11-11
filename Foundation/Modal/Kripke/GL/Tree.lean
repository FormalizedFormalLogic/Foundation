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
  simp at h;
  intro T;
  apply @h T.toFrame;
  simp [FiniteFrameClass.toFrameClass];
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
  constructor;
  . contrapose; simp; apply provable_iff_satisfies_at_root_on_FiniteTransitiveTree.mpr;
  . contrapose; simp; apply provable_iff_satisfies_at_root_on_FiniteTransitiveTree.mp;

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
    simp at w;
    match w with
    | .inl _ => simp;
    | .inr x => simp [Frame.Rel]
  rel_assymetric := by
    simp_all;
    intro x y hxy;
    match x, y with
    | .inl x, _ => simp;
    | .inr x, .inr y => exact F.rel_assymetric hxy;
  rel_transitive := by
    simp_all;
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
    | .inr y => use y; simp; exact h;

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

lemma modal_equivalence_original_world {x : M.toModel.World} : ModalEquivalent (M₁ := M.toModel) (M₂ := (M↧).toModel) x x := by
  apply Model.PseudoEpimorphism.modal_equivalence p_morphism;

end FiniteTransitiveTreeModel.SimpleExtension

end Kripke


namespace Hilbert.GL

open System
open Formula.Kripke (Satisfies)
open Kripke
open Kripke.FiniteTransitiveTreeModel

variable {φ ψ : Formula ℕ}

/-
  逆は以下を順に辿って構文論的に証明できる．
  - `System.imply_boxdot_boxdot_of_imply_boxdot_plain`
  - `System.imply_boxdot_axiomT_of_imply_boxdot_boxdot`
  - `System.imply_box_box_of_imply_boxdot_axiomT`
-/
lemma imply_boxdot_plain_of_imply_box_box : (Hilbert.GL ℕ) ⊢! □φ ➝ □ψ → (Hilbert.GL ℕ) ⊢! ⊡φ ➝ ψ := by
  contrapose;
  intro h;
  have := Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mp h;
  obtain ⟨M, hs⟩ := this;
  have hs : Satisfies M.toModel M.root (⊡φ ⋏ ∼ψ) := by simp_all [Satisfies, Semantics.Realize];
  replace hs := @SimpleExtension.modal_equivalence_original_world M M.root (⊡φ ⋏ ∼ψ) |>.mp hs;

  simp [Satisfies, Semantics.Realize] at hs;
  have ⟨hs₁, hs₂, hs₃⟩ := hs;

  have hbp : Satisfies M↧.toModel (M↧.root) (□φ) := by
    intro x hx;
    rcases @Kripke.FiniteTransitiveTree.SimpleExtension.through_original_root M.toFiniteTransitiveTree x hx with (rfl | hr);
    . assumption;
    . apply hs₂;
      exact hr;
  have hbq : ¬(Satisfies M↧.toModel (M↧.root) (□ψ)) := by
    simp [Satisfies];
    use M.root;
    constructor;
    . apply M↧.toRootedFrame.root_rooted M.root;
      simp [SimpleExtension, Kripke.FiniteTransitiveTree.SimpleExtension]; -- TODO: extract lemma
    . assumption;

  apply Kripke.unprovable_iff_exists_unsatisfies_at_root_on_FiniteTransitiveTree.mpr;
  use M↧;
  exact _root_.not_imp.mpr ⟨hbp, hbq⟩;

theorem unnecessitation! : (Hilbert.GL ℕ) ⊢! □φ → (Hilbert.GL ℕ) ⊢! φ := by
  intro h;
  have : (Hilbert.GL ℕ) ⊢! □⊤ ➝ □φ := imply₁'! (ψ := □⊤) h;
  have : (Hilbert.GL ℕ) ⊢! ⊡⊤ ➝ φ := imply_boxdot_plain_of_imply_box_box this;
  exact this ⨀ boxdotverum!;

noncomputable instance : System.Unnecessitation (Hilbert.GL ℕ) where
  unnec := λ h => Hilbert.GL.unnecessitation! ⟨h⟩ |>.some

end Hilbert.GL


end LO.Modal

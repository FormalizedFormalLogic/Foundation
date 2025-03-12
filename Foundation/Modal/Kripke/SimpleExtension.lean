import Foundation.Modal.Kripke.Tree
import Mathlib.Data.Finite.Sum

namespace LO.Modal.Kripke

def Frame.extendRoot (F : Kripke.Frame) (r : F.World) [F.IsRooted r] : Kripke.Frame where
  World := Unit ⊕ F.World
  Rel x y :=
    match x, y with
    | .inr x, .inr y => x ≺ y
    | .inl _, .inr _ => True
    | _ , _ => False

namespace Frame.extendRoot

variable {F : Frame} {r : F.World} [F.IsRooted r] {x y : F.World}

instance [f : F.IsFinite] : (F.extendRoot r).IsFinite := by
  unfold Frame.extendRoot;
  apply Frame.isFinite_iff _ |>.mpr;
  infer_instance;

protected abbrev root : (F.extendRoot r).World := .inl ()

instance instIsRooted : (F.extendRoot r).IsRooted extendRoot.root where
  root_generates := by
    intro x h;
    match x with
    | .inl _ => contradiction;
    | .inr x => apply Relation.TransGen.single; tauto;

lemma rel_assymetric (F_assym : Assymetric F) : Assymetric (F.extendRoot r).Rel := by
  intro x y hxy;
  match x, y with
  | .inl x, _ => simp_all [Frame.extendRoot]
  | .inr x, .inr y => exact F_assym hxy;

lemma rel_transitive (F_trans : Transitive F) : Transitive (F.extendRoot r).Rel := by
  intro x y z hxy hyz;
  match x, y, z with
  | .inl _, .inr _, .inr _ => simp_all [Frame.extendRoot]
  | .inr x, .inr y, .inr z => exact F_trans hxy hyz;

instance {r : F.World} [tree : F.IsTree r] : (F.extendRoot r).IsTree extendRoot.root where
  rel_assymetric := rel_assymetric $ tree.rel_assymetric;
  rel_transitive := rel_transitive $ tree.rel_transitive

instance [F.IsFiniteTree r] : (F.extendRoot r).IsFiniteTree (extendRoot.root) where

def pMorphism : F →ₚ (F.extendRoot r) where
  toFun := Sum.inr
  forth := by simp [Frame.extendRoot];
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', Frame.extendRoot] at h;
    | .inr y => use y; simpa using h;

lemma through_original_root [F.IsTree r] {x : (F.extendRoot r).World} (h : extendRoot.root ≺ x) : x = extendRoot.root ∨ (Sum.inr r ≺^+ x) := by
  match x with
  | .inl x => simp;
  | .inr x =>
    by_cases e : x = r;
    . subst e;
      sorry;
    . right;
      apply Relation.TransGen.single;
      apply pMorphism (F := F).forth;
      sorry;

end Frame.extendRoot


abbrev Model.extendRoot (M : Kripke.Model) (r : M.World) [M.IsRooted r] : Kripke.Model where
  toFrame := M.toFrame.extendRoot r
  Val x a :=
    match x with
    | .inl _ => M.Val r a
    | .inr x => M.Val x a

namespace Model.extendRoot

variable {M : Model} {r : M.World} [M.IsRooted r] {x y : M.World}

def pMorphism : Model.PseudoEpimorphism M (M.extendRoot r) := Model.PseudoEpimorphism.ofAtomic (@Frame.extendRoot.pMorphism M.toFrame r inferInstance) $ by
  intros; rfl;

lemma modal_equivalence_original_world {x : M.World} : ModalEquivalent (M₁ := M) (M₂ := M.extendRoot r) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence pMorphism;

end Model.extendRoot


end LO.Modal.Kripke

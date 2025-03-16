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

instance : Coe (F.World) ((F.extendRoot r).World) := ⟨Sum.inr⟩

instance [Finite F.World] : Finite (F.extendRoot r).World := by
  unfold Frame.extendRoot;
  infer_instance;

protected abbrev root : (F.extendRoot r).World := .inl ()

instance instIsRooted : (F.extendRoot r).IsRooted extendRoot.root where
  root_generates := by
    intro x h;
    match x with
    | .inl _ => contradiction;
    | .inr x => apply Relation.TransGen.single; tauto;

protected lemma rel_assymetric (F_assym : Assymetric F) : Assymetric (F.extendRoot r).Rel := by
  intro x y hxy;
  match x, y with
  | .inl x, _ => simp_all [Frame.extendRoot]
  | .inr x, .inr y => exact F_assym hxy;

protected lemma rel_transitive (F_trans : Transitive F) : Transitive (F.extendRoot r).Rel := by
  intro x y z hxy hyz;
  match x, y, z with
  | .inl _, .inr _, .inr _ => simp_all [Frame.extendRoot]
  | .inr x, .inr y, .inr z => exact F_trans hxy hyz;

protected instance instIsTree {r : F.World} [F.IsTree r] : (F.extendRoot r).IsTree extendRoot.root where
  rel_assymetric := extendRoot.rel_assymetric $ IsTree.rel_assymetric (F := F) (r := r)
  rel_transitive := extendRoot.rel_transitive $ IsTree.rel_transitive (F := F) (r := r)

protected instance instIsFiniteTree [F.IsFinite] [F.IsTree r] : (F.extendRoot r).IsFiniteTree extendRoot.root := by
  have := @extendRoot.instIsTree F r;
  tauto;

def pMorphism : F →ₚ (F.extendRoot r) where
  toFun := Sum.inr
  forth := by simp [Frame.extendRoot];
  back {x y} h := by
    match y with
    | .inl r => simp [Frame.Rel', Frame.extendRoot] at h;
    | .inr y => use y; simpa using h;

lemma through_original_root [F.IsTree r] {x : (F.extendRoot r).World} (h : extendRoot.root ≺ x) : x = r ∨ (Sum.inr r ≺^+ x) := by
  match x with
  | .inl x =>
    have := Frame.IsTree.rel_irreflexive (F := (F.extendRoot r)) (r := (extendRoot.root));
    contradiction
  | .inr x =>
    by_cases e : x = r;
    . tauto;
    . right;
      apply Relation.TransGen.single;
      apply pMorphism (F := F).forth;
      exact IsRooted.root_generates x (by tauto) |>.unwrap $ IsTree.rel_transitive (r := r);

end Frame.extendRoot


def Model.extendRoot (M : Kripke.Model) (r : M.World) [M.IsRooted r] : Kripke.Model where
  toFrame := M.toFrame.extendRoot r
  Val x a :=
    match x with
    | .inl _ => M.Val r a
    | .inr x => M.Val x a

namespace Model.extendRoot

variable {M : Model} {r : M.World} [M.IsRooted r] {x y : M.World}

protected abbrev root := Frame.extendRoot.root (F := M.toFrame) (r := r)

def pMorphism : Model.PseudoEpimorphism M (M.extendRoot r) := PseudoEpimorphism.ofAtomic (Frame.extendRoot.pMorphism (F := M.toFrame) (r := r)) $ by
  intros; rfl;

lemma modal_equivalence_original_world {x : M.World} : ModalEquivalent (M₁ := M) (M₂ := M.extendRoot r) x (Sum.inr x) := by
  apply Model.PseudoEpimorphism.modal_equivalence pMorphism;

end Model.extendRoot


end LO.Modal.Kripke

import Foundation.Vorspiel.Chain
import Foundation.Modal.Kripke2.Preservation
import Foundation.Modal.Kripke2.FiniteFrame

namespace LO.Modal


structure Kripke.FiniteTransitiveTree extends Kripke.FiniteFrame, Kripke.RootedFrame where
  rel_assymetric : Assymetric Rel
  rel_transitive : Transitive Rel

namespace Kripke.FiniteTransitiveTree

lemma rel_irreflexive (T : FiniteTransitiveTree) : Irreflexive T.Rel := irreflexive_of_assymetric $ T.rel_assymetric

end Kripke.FiniteTransitiveTree


def Formula.Kripke.ValidOnFiniteTransitiveTreeFrame (T : Kripke.FiniteTransitiveTree) (φ : Formula ℕ) := T.toFrame ⊧ φ

namespace ValidOnFiniteTransitiveTreeFrame

instance semantics : Semantics (Formula ℕ) (Kripke.FiniteFrame) := ⟨fun F ↦ Formula.Kripke.ValidOnFiniteFrame F⟩

end ValidOnFiniteTransitiveTreeFrame


namespace Kripke

open Relation (TransGen)

structure FiniteTransitiveTreeModel extends FiniteTransitiveTree, Model where

variable {F : Frame} {r : F.World}

def Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1
  world_nonempty := ⟨[r], (by simp)⟩

namespace Frame.TreeUnravelling

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_length {x y : (F.TreeUnravelling r).World} (h : x ≺ y) : x.1.length < y.1.length := by
  obtain ⟨z, hz⟩ := h;
  rw [←hz];
  simp;

lemma irreflexive : Irreflexive (F.TreeUnravelling r).Rel := by
  intro x; simp [TreeUnravelling];

lemma assymetric : Assymetric (F.TreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

def PMorphism (F : Frame) (r : F) : F.TreeUnravelling r →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    obtain ⟨z, hz⟩ := h;
    have ⟨_, _, h⟩ := @List.chain'_append _ F.Rel cx.1 [z] |>.mp (by rw [hz]; exact cy.2.2);
    refine h (cx.1.getLast (by aesop)) ?hx (cy.1.getLast (by aesop)) ?hy;
    . exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    . rw [←@List.getLast_append_singleton _ z cx.1]; simp_all;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . use y;
    . constructor;
      . obtain ⟨i, hi⟩ := cx.2.1;
        use (i ++ [y]);
        simp_rw [←List.append_assoc, hi];
      . apply List.Chain'.append;
        . exact cx.2.2;
        . simp;
        . intro z hz; simp;
          convert h;
          exact List.mem_getLast?_eq_getLast hz |>.2;

end Frame.TreeUnravelling


abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := (F.TreeUnravelling r)^+

namespace Frame.TransitiveTreeUnravelling

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_length {x y : (F.TransitiveTreeUnravelling r).World} (Rxy : x ≺ y) : x.1.length < y.1.length := by
  induction Rxy with
  | single Rxy => exact TreeUnravelling.rel_length Rxy;
  | tail _ h ih => have := TreeUnravelling.rel_length h; omega;

lemma rel_transitive : Transitive (F.TransitiveTreeUnravelling r) := TransitiveClosure.rel_transitive

lemma rel_asymmetric : Assymetric (F.TransitiveTreeUnravelling r).Rel := by
  rintro x y hxy;
  by_contra hyx;
  replace hxy := rel_length hxy;
  replace hyx := rel_length hyx;
  exact hxy.not_lt hyx;

lemma rel_def {x y : (F.TransitiveTreeUnravelling r).World} : x ≺ y ↔ (x.1.length < y.1.length ∧ x.1 <+: y.1) := by
  constructor;
  . intro Rxy;
    induction Rxy with
    | single Rxy =>
      obtain ⟨z, hz⟩ := Rxy;
      rw [←hz];
      constructor;
      . simp;
      . use [z];
    | tail _ h ih =>
      obtain ⟨w, hw⟩ := h;
      obtain ⟨_, ⟨zs, hzs⟩⟩ := ih;
      rw [←hw, ←hzs];
      constructor;
      . simp;
      . use zs ++ [w];
        simp [List.append_assoc];
  . replace ⟨xs, ⟨ws, hw⟩, hx₂⟩ := x;
    replace ⟨ys, ⟨vs, hv⟩, hy₂⟩ := y;
    subst hw hv;
    rintro ⟨hl, ⟨zs, hzs⟩⟩;
    simp at hzs;
    induction zs using List.induction_with_singleton generalizing ws vs with
    | hnil => simp_all;
    | hsingle z =>
      apply TransGen.single;
      use z;
      simp_all;
    | hcons z zs h ih =>
      simp_all;
      refine TransGen.head ?h₁ $ ih (ws ++ [z]) vs ?h₂ ?h₃ ?h₄ ?h₅;
      . use z; simp;
      . apply List.Chain'.prefix hy₂;
        use zs; simp_all;
      . exact hy₂;
      . rw [←hzs]; simp;
        by_contra hC;
        simp_all;
      . simp_all;

lemma rooted : (F.TransitiveTreeUnravelling r).isRooted ⟨[r], by tauto⟩ := by
  intro x ha;
  apply rel_def.mpr;
  obtain ⟨zs, hzs⟩ := x.2.1;
  constructor;
  . rw [←hzs];
    by_contra hC;
    simp at hC;
    simp_all;
  . use zs;

abbrev pMorphism (F : Frame) (F_trans : Transitive F.Rel) (r : F) : (F.TransitiveTreeUnravelling r) →ₚ F := (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans

end Frame.TransitiveTreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model where
  toFrame := M.toFrame.TreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a

namespace Model.TreeUnravelling

variable {M : Kripke.Model} {r : M.World}

def pMorphism (M : Kripke.Model) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.TreeUnravelling.PMorphism M.toFrame r) $ by aesop;

end Model.TreeUnravelling


def Model.TransitiveTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model where
  toFrame := M.toFrame.TransitiveTreeUnravelling r
  Val c a := M.Val (c.1.getLast (by simp)) a

namespace Model.TransitiveTreeUnravelling

abbrev pMorphism (M : Kripke.Model) (M_trans : Transitive M.Rel) (r : M.World) : M.TransitiveTreeUnravelling r →ₚ M :=
  PseudoEpimorphism.ofAtomic (Frame.TransitiveTreeUnravelling.pMorphism M.toFrame M_trans r) $ by aesop;

lemma modal_equivalence_at_root (M : Kripke.Model) (M_trans : Transitive M.Rel) (r : M.World)
  : ModalEquivalent (M₁ := M.TransitiveTreeUnravelling r) (M₂ := M) ⟨[r], by simp⟩ r
  := Model.PseudoEpimorphism.modal_equivalence (Model.TransitiveTreeUnravelling.pMorphism M M_trans r) (⟨[r], by simp⟩)

end Model.TransitiveTreeUnravelling


abbrev Model.FiniteTransitiveTreeUnravelling (M : Kripke.Model) (r : M.World) : Kripke.Model := (M↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩

abbrev FiniteFrame.FiniteTransitiveTreeUnravelling
  (F : FiniteFrame) [DecidableEq F.World] (F_trans : Transitive F.toFrame) (F_irrefl : Irreflexive F.toFrame) (r : F.World) : FiniteTransitiveTree :=
  letI T := (F.toFrame↾r).TransitiveTreeUnravelling ⟨r, by tauto⟩
  {
    World := T.World
    Rel := T.Rel
    rel_transitive := Frame.TransitiveTreeUnravelling.rel_transitive
    rel_assymetric := Frame.TransitiveTreeUnravelling.rel_asymmetric
    root_rooted := Frame.TransitiveTreeUnravelling.rooted
    world_finite := by
      suffices h : Finite { x // List.Chain' (F.PointGenerated r).Rel x } by
        exact
          Finite.of_injective
          (β := { x // List.Chain' (F.PointGenerated r).Rel x })
          (fun x => ⟨x.1, x.2.2⟩)
          (by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp_all);
      exact List.chains_finite (Frame.PointGenerated.rel_transitive F_trans) (Frame.PointGenerated.rel_irreflexive F_irrefl)
  }

end Kripke

end LO.Modal

import Logic.Modal.Standard.Kripke.GL
import Logic.Modal.Standard.Kripke.Preservation

def Assymetric (rel : α → α → Prop) := ∀ ⦃x y⦄, (rel x y) → ¬(rel x y)

lemma irreflexive_of_assymetric (h : Assymetric rel) : Irreflexive rel := by simp_all [Assymetric, Irreflexive];

-- TODO: move
lemma List.last_length_1 {α} {l : List α} (h : l.length = 1) : l = [l.getLast (by aesop)] := by
  match l with
  | [r] => rfl

-- TODO: move
lemma List.interpolant {α} {l₁ l₂ : List α} (h_length : l₁.length + 1 = l₂.length) (h_prefix : l₁ <+: l₂)
  : ∃ z, l₁ ++ [z] = l₂ := by
    obtain ⟨l₃, rfl⟩ := h_prefix;
    use l₃.getLast (by aesop);
    have : l₃ = [l₃.getLast _] := List.last_length_1 (by simp_all);
    rw [←this];

-- TODO: is exists?
lemma List.head?_eq_head_of_ne_nil {l : List α} (h : l ≠ []) : l.head? = some (l.head h):= by
  induction l with
  | nil => contradiction;
  | cons => simp_all;

namespace LO.Modal.Standard

namespace Kripke

-- open System
open Kripke
open Formula.Kripke

variable {α} [Inhabited α] [DecidableEq α]

open Relation (TransGen ReflTransGen)


def Frame.isStrictRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w

def Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w, r ≺ w


namespace Frame

variable {F : Kripke.Frame} (x : F.World)

def successors := { w // x ≺^* w }
postfix:100 "↑*" => Frame.upward

def immediate_successors := { w // x ≺ w }
postfix:100 "↑¹" => Frame.immediate_successor

def proper_immediate_successors := { w // x ≠ w ∧ x ≺ w }
postfix:100 "↑" => Frame.proper_immediate_successor


def predeccsors := { w // w ≺^* x }
postfix:100 "↓*" => Frame.downward

def immediate_predeccsors := { w // w ≺ x }
postfix:100 "↓¹" => Frame.immediate_predeccsor

def proper_immediate_predeccsors := { w // w ≠ x ∧ w ≺ x }
postfix:100 "↓" => Frame.proper_immediate_predeccsors

end Frame


@[simp]
lemma Frame.strictly_rooted_of_rooted {F : Frame} {r : F.World} (h : F.isRooted r) : F.isStrictRooted r := by
  intros w _;
  exact h w;

structure RootedFrame extends Kripke.Frame where
  root : World
  def_root : ∀ w ≠ root, root ≺^* w
  -- no_root_cycle : ∀ w ≠ root, ¬(w ≺^* root)
  default := root

section

def Frame.PointGenerated (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w | w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  default := ⟨r, by tauto⟩
infix:100 "↾" => Frame.PointGenerated


def Model.PointGenerated (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := (M.Frame↾r)
  Valuation w a := M.Valuation w.1 a
infix:100 "↾" => Model.PointGenerated

def Model.PointGenerated.Bisimulation (M : Model α) (M_trans : Transitive M.Frame) (r : M.World): (M↾r) ⇄ M where
  toRel x y := x.1 = y
  atomic := by
    rintro x y a rfl;
    simp [Model.PointGenerated];
  forth := by
    rintro x₁ y₁ x₂ rfl Rx₂y₁;
    use y₁.1;
    constructor;
    . simp;
    . exact Rx₂y₁;
  back := by
    rintro ⟨x₁, (rfl | hx₁)⟩ x₂ y₂ rfl Rx₂y₂;
    . use ⟨y₂, by right; exact Rx₂y₂⟩;
      constructor;
      . simp;
      . exact Rx₂y₂;
    . use ⟨y₂, ?h₂⟩;
      constructor;
      . simp;
      . exact Rx₂y₂;
      right;
      exact M_trans hx₁ Rx₂y₂;

lemma Model.PointGenerated.Bisimulation.rooted (M_trans : Transitive M.Frame := by assumption) : (Bisimulation M M_trans r) ⟨r, by simp⟩ r := by simp [Bisimulation];

lemma Model.PointGenerated.modal_equivalent_to_root (M_trans : Transitive M.Frame) : ModalEquivalent (M₁ := M↾r) (M₂ := M) ⟨r, by simp⟩ r
  := modal_equivalent_of_bisimilar (Bisimulation M M_trans r) Bisimulation.rooted


-- TODO: move
section S5

def _root_.Universal {α} (R : α → α → Prop) : Prop := ∀ ⦃x y : α⦄, R x y

lemma _root_.refl_of_universal (h : Universal R) : Reflexive R := by
  intro x; exact @h x x;

lemma _root_.eucl_of_universal (h : Universal R) : Euclidean R := by
  rintro x y z _ _; exact @h z y;

lemma Frame.PointGenerated.rel_universal
  {F : Kripke.Frame} {r : F.World} (F_refl : Reflexive F) (F_eucl : Euclidean F) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl F_eucl;
  simp [Frame.PointGenerated];
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply F_refl;
  . exact hy;
  . exact F_symm hx;
  . apply F_symm $ F_eucl hx hy;

abbrev UniversalFrameClass : FrameClass := { F | Universal F }

lemma iff_Universal_ReflexiveEuclidean_validOnFrameClass : UniversalFrameClass.{u}# ⊧ p ↔ ReflexiveEuclideanFrameClass.{u}# ⊧ p := by
  constructor;
  . intro h F hF V r;
    apply Model.PointGenerated.modal_equivalent_to_root (by apply trans_of_refl_eucl hF.1 hF.2) |>.mp;
    apply @h (F↾r) (Frame.PointGenerated.rel_universal hF.1 hF.2) ((⟨F, V⟩)↾r).Valuation;
  . rintro h F F_univ;
    exact @h F (⟨refl_of_universal F_univ, eucl_of_universal F_univ⟩);

instance S5_complete_universal : Complete (𝐒𝟓 : DeductionParameter α) UniversalFrameClass# := ⟨by
  intro p hF;
  have : ReflexiveEuclideanFrameClass# ⊧ p := iff_Universal_ReflexiveEuclidean_validOnFrameClass.mp hF;
  exact S5_complete.complete this;
⟩

end S5



structure Tree extends Kripke.RootedFrame where
  goback : ∀ w ≠ root, ∃! x : w↓, w ≺ x.1

structure TransitiveTree extends Kripke.Tree where
  rel_irreflexive : Irreflexive Rel
  rel_transitive : Transitive Rel

structure FiniteTransitiveTree extends TransitiveTree, FiniteFrame where

set_option linter.unusedVariables false in
protected abbrev FiniteTransitiveTree.Dep (α : Type*) := FiniteTransitiveTree
protected abbrev FiniteTransitiveTree.alt (T : FiniteTransitiveTree) {α} : FiniteTransitiveTree.Dep α := T
postfix:max "#" => FiniteTransitiveTree.alt

namespace FiniteTransitiveTree

instance : Semantics (Formula α) (FiniteTransitiveTree.Dep α) := ⟨fun T ↦ Formula.Kripke.ValidOnFrame T.toFrame⟩

end FiniteTransitiveTree


section TreeUnravelling

def Frame.TreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  default := ⟨[r], (by simp)⟩
  Rel cx cy := ∃ z, cx.1 ++ [z] = cy.1

namespace Frame.TreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.TreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma irreflexive : Irreflexive (F.TreeUnravelling r).Rel := by
  intro x; simp [TreeUnravelling];

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

variable (hr : F.isRooted r)

@[simp]
lemma PMorphism.surjective_of_rooted : Function.Surjective (PMorphism F r) := by
  intro x;
  use ⟨[r, x], ?_⟩
  simp [PMorphism];
  constructor;
  . use [x]; simp;
  . simp; exact hr x;

lemma validOnBaseFrame : (F.TreeUnravelling r)# ⊧ p → F# ⊧ p
  := iff_formula_valid_on_frame_surjective_morphism (PMorphism F r) (by simp_all)

end Frame.TreeUnravelling


def Model.TreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TreeUnravelling

variable {M : Kripke.Model α} {r : M.World} {p : Formula α}

def PMorphism (M : Kripke.Model α) (r : M.World) : M.TreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TreeUnravelling.PMorphism M.Frame r) $ by aesop;

end Model.TreeUnravelling

end TreeUnravelling

-- TODO: move
def Frame.PseudoEpimorphism.TransitiveClosure {F₁ F₂ : Frame} (f : F₁ →ₚ F₂) (F₂_trans : Transitive F₂) : F₁^+ →ₚ F₂ where
  toFun := f.toFun
  forth := by
    intro x y hxy; simp at x y;
    induction hxy with
    | single hxy => exact f.forth hxy;
    | @tail z y _ Rzy Rxz =>
      replace Rzy := f.forth Rzy;
      exact F₂_trans Rxz Rzy;
  back := by
    intro x w hxw;
    obtain ⟨u, ⟨rfl, hxu⟩⟩ := f.back hxw;
    use u;
    constructor;
    . rfl;
    . exact RelTransGen.single hxu;


section TransitiveTreeUnravelling

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := (F.TreeUnravelling r)^+

namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

lemma rel_transitive : Transitive (F.TransitiveTreeUnravelling r) := TransitiveClosure.rel_transitive

/-
lemma rel_irreflexive : Irreflexive (F.TransitiveTreeUnravelling r).Rel := by
  simp [TransitiveTreeUnravelling, TreeUnravelling];
  rintro x Rxx;
  cases Rxx with
  | single h => exact TreeUnravelling.irreflexive x h;
  | tail Rxw Rwx =>
    induction Rxw with
    | single => aesop;
    | tail Rxv Rvw ih => sorry;

lemma rel_branching : ∀ x : (F.TransitiveTreeUnravelling r).World, ∀ y z : x↓, y ≠ z → (y.1 ≺ z.1 ∨ z.1 ≺ y.1) := by sorry;
-/


def PMorphism (F : Frame) (F_trans : Transitive F.Rel) (r : F) : (F.TransitiveTreeUnravelling r) →ₚ F := (Frame.TreeUnravelling.PMorphism F r).TransitiveClosure F_trans

end Frame.TransitiveTreeUnravelling


def Model.TransitiveTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.TransitiveTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.TransitiveTreeUnravelling

variable {M : Kripke.Model α} {r : M.World} {p : Formula α}

def PMorphism (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World) : M.TransitiveTreeUnravelling r →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.TransitiveTreeUnravelling.PMorphism M.Frame M_trans r) $ by aesop;

end Model.TransitiveTreeUnravelling


end TransitiveTreeUnravelling



section GLTreeUnravelling

def Frame.GLTreeUnravelling (F : Frame) (r : F.World) : Kripke.Frame where
  World := { c : List F.World | [r] <+: c ∧ c.Chain' F.Rel }
  default := ⟨[r], (by simp)⟩
  Rel cx cy := cx.1.length < cy.1.length ∧ cx.1 <+: cy.1

namespace Frame.GLTreeUnravelling

variable {F : Frame} {r : F.World}

@[simp]
lemma not_nil {c : (F.GLTreeUnravelling r).World} : c.1 ≠ [] := by
  have := c.2.1;
  by_contra;
  simp_all;

lemma rel_transitive : Transitive (F.GLTreeUnravelling r).Rel := by
  rintro x y z ⟨hxz, ⟨w, hxwy⟩⟩ ⟨hyz, ⟨v, hyvz⟩⟩;
  constructor;
  . omega;
  . use (w ++ v);
    simp_rw [←List.append_assoc, hxwy, hyvz];

lemma rel_irreflexive : Irreflexive (F.GLTreeUnravelling r).Rel := by
  simp [Irreflexive, GLTreeUnravelling];

def PMorphism (F : Frame) (F_trans : Transitive F) (r : F.World) : (F.GLTreeUnravelling r) →ₚ F where
  toFun c := c.1.getLast (by simp)
  forth {cx cy} h := by
    simp;
    obtain ⟨hl, ⟨cz, hz⟩⟩ := h;
    wlog cz_nnil : cz ≠ []
    case inr => simp_all only [Set.mem_setOf_eq, ne_eq, forall_const, not_not, List.append_nil, lt_self_iff_false];
    have ⟨_, cz_chain, h⟩ := @List.chain'_append _ F.Rel cx.1 cz |>.mp (by rw [hz]; exact cy.2.2);
    have h₁ := h (cx.1.getLast (by aesop)) ?hx (cz.head (by assumption)) ?hz;
    case hx => exact List.getLast?_eq_getLast_of_ne_nil (by simp);
    case hz => exact List.head?_eq_head_of_ne_nil _;
    apply F_trans h₁;
    suffices h : F.Rel (cz.head (by assumption)) (cz.getLast (by assumption)) by
      have := List.getLast_append' (l₁ := cx.1) (l₂ := cz) (by assumption);
      simp_all;
    sorry;
  back {cx y} h := by
    simp_all;
    use ⟨cx.1 ++ [y], ?_⟩;
    . constructor;
      . simp;
      . constructor;
        . simp;
        . use [y];
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

end Frame.GLTreeUnravelling


def Model.GLTreeUnravelling (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := M.Frame.GLTreeUnravelling r
  Valuation c a := M.Valuation (c.1.getLast (by simp)) a

namespace Model.GLTreeUnravelling

variable (M : Kripke.Model α) (M_trans : Transitive M.Frame) (r : M.World) {p : Formula α}

def PMorphism : (M.GLTreeUnravelling r) →ₚ M :=
  Model.PseudoEpimorphism.mkAtomic (Frame.GLTreeUnravelling.PMorphism M.Frame M_trans r) $ by aesop;

lemma modal_equivalence {w : M.GLTreeUnravelling r} : w ↭ (w.1.getLast (by simp)) := by
  have H := @modal_equivalence_of_modal_morphism _ (M.GLTreeUnravelling r) M (PMorphism M M_trans r) w;
  intro p;
  have Hp := @H p;
  constructor;
  . intro hp; exact Hp.mp hp;
  . intro hp; exact Hp.mpr hp;

end Model.GLTreeUnravelling

end GLTreeUnravelling



variable {p : Formula α}

lemma validOnFTT_Aux (h : TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, T# ⊧ p := by
  simp at h;
  intro T;
  apply @h T.toFrame T.toFiniteFrame;
  . exact T.rel_transitive;
  . exact T.rel_irreflexive;
  . tauto;

lemma validOnFTT_root (h : ∀ F : FiniteTransitiveTree.{u}, F# ⊧ p) : ∀ T : FiniteTransitiveTree.{u}, ∀ V, Satisfies ⟨T.toFrame, V⟩ T.root p := by
  intro T V; exact h T V _;

-- set_option pp.proofs true in
lemma validOnFTT_root' : (∀ T : FiniteTransitiveTree.{u}, ∀ V, Satisfies ⟨T.toFrame, V⟩ T.root p) → TransitiveIrreflexiveFrameClass.{u}ꟳ# ⊧ p := by
  contrapose; push_neg;
  intro h; simp [ValidOnFrame, ValidOnModel] at h;
  obtain ⟨_, F, F_trans, F_irrefl, rfl, V, x, hx⟩ := h;
  have := @Model.GLTreeUnravelling.modal_equivalence _ ⟨F, V⟩ F_trans x ⟨[x], by simp⟩ p |>.not.mpr hx;
  sorry;

end

end Kripke

end LO.Modal.Standard

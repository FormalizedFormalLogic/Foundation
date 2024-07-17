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

@[simp]
lemma Frame.strictly_rooted_of_rooted {F : Frame} {r : F.World} (h : F.isRooted r) : F.isStrictRooted r := by
  intros w _;
  exact h w;

structure RootedFrame extends Kripke.Frame where
  root : World
  default := root
  def_root : ∀ w, root ≺ w

section

/-- point generated -/
def Frame.Cuttage (F : Kripke.Frame) (r : F.World) : Kripke.RootedFrame where
  World := { w | w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  root := ⟨r, by tauto⟩
  def_root := by sorry
infix:100 "↾" => Frame.Cuttage


def Model.Cuttage (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := (M.Frame↾r).toFrame
  Valuation w a := M.Valuation w.1 a
infix:100 "↾" => Model.Cuttage


def Frame.downward {F : Kripke.Frame} (x : F.World) : Type u := { w // w ≺^+ x }
postfix:100 "↓" => Frame.downward

structure Tree extends Kripke.RootedFrame where
  branching : ∀ x : World, ∀ y z : x↓, y ≠ z → (y.1 ≺ z.1 ∨ z.1 ≺ y.1) -- linear order

structure TransitiveTree extends Kripke.Tree where
  rel_irreflexive : Irreflexive Rel
  rel_transitive : Transitive Rel

structure FiniteTransitiveTree extends TransitiveTree, FiniteFrame where

set_option linter.unusedVariables false in
protected abbrev FiniteTransitiveTree.Dep (α : Type u) := FiniteTransitiveTree
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


section TransitiveTreeUnravelling

abbrev Frame.TransitiveTreeUnravelling (F : Frame) (r : F.World) := F.TreeUnravelling r |>.TransitiveClosure

namespace Frame.TransitiveTreeUnravelling

variable {F : Frame} {r : F.World} {p : Formula α}

@[simp]
lemma not_nil {c : (F.TransitiveTreeUnravelling r).World} : c.1 ≠ [] := by
  by_contra;
  have := c.2.1;
  simp_all;

@[simp] lemma transitive : Transitive (F.TransitiveTreeUnravelling r) := by simp

end Frame.TransitiveTreeUnravelling

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

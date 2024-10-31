import Foundation.Logic.Kripke.Basic
import Foundation.Logic.Kripke.Closure

namespace LO.Kripke

section Bisimulation

structure Model.Bisimulation (M₁ M₂ : Kripke.Model α) where
  toRel : Rel M₁.World M₂.World
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : α} : toRel x₁ x₂ → ((M₁.Valuation x₁ a) ↔ (M₂.Valuation x₂ a))
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ " => Model.Bisimulation

instance : CoeFun (Model.Bisimulation M₁ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨λ bi => bi.toRel⟩

end Bisimulation



section PseudoEpimorphism

structure Frame.PseudoEpimorphism (F₁ F₂ : Kripke.Frame) where
  toFun : F₁.World → F₂.World
  forth {x y : F₁.World} : x ≺ y → toFun x ≺ toFun y
  back {w : F₁.World} {v : F₂.World} : toFun w ≺ v → ∃ u, toFun u = v ∧ w ≺ u

infix:80 " →ₚ " => Frame.PseudoEpimorphism

instance : CoeFun (Frame.PseudoEpimorphism F₁ F₂) (λ _ => F₁.World → F₂.World) := ⟨λ f => f.toFun⟩

namespace Frame.PseudoEpimorphism

variable {F F₁ F₂ F₃ : Kripke.Frame}

def id : F →ₚ F where
  toFun := _root_.id
  forth := by simp;
  back := by simp;

def TransitiveClosure (f : F₁ →ₚ F₂) (F₂_trans : Transitive F₂) : F₁^+ →ₚ F₂ where
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
    . exact Frame.RelTransGen.single hxu;

def comp (f : F₁ →ₚ F₂) (g : F₂ →ₚ F₃) : F₁ →ₚ F₃ where
  toFun := g ∘ f
  forth := by
    intro x y hxy;
    exact g.forth $ f.forth hxy;
  back := by
    intro x w hxw;
    simp at hxw;
    obtain ⟨y, ⟨hyz, hxy⟩⟩ := g.back hxw;
    obtain ⟨u, ⟨hgu, hfu⟩⟩ := f.back hxy;
    use u;
    constructor;
    . subst_vars; simp;
    . assumption;

end Frame.PseudoEpimorphism


structure Model.PseudoEpimorphism (M₁ M₂ : Kripke.Model α) extends M₁.Frame →ₚ M₂.Frame where
  atomic {w : M₁.World} {a} : (M₁.Valuation w a) ↔ (M₂.Valuation (toFun w) a)

infix:80 " →ₚ " => Model.PseudoEpimorphism

instance : CoeFun (Model.PseudoEpimorphism M₁ M₂) (λ _ => M₁.World → M₂.World) := ⟨λ f => f.toFun⟩

namespace Model.PseudoEpimorphism

variable {M M₁ M₂ M₃ : Kripke.Model α}

def toFramePseudoEpimorphism (f : M₁ →ₚ M₂) : M₁.Frame →ₚ M₂.Frame where
  toFun := f.toFun
  forth := f.forth
  back := f.back

def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp;
  back := by simp;
  atomic := by simp;

def mkAtomic
  (f : M₁.Frame →ₚ M₂.Frame) (atomic : ∀ {w a}, (M₁.Valuation w a) ↔ (M₂.Valuation (f w) a))
  : M₁ →ₚ M₂
  := {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := atomic,
  }

def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ := mkAtomic (f.toFramePseudoEpimorphism.comp (g.toFramePseudoEpimorphism)) $ by
    intro x φ;
    constructor;
    . intro h;
      apply g.atomic.mp;
      apply f.atomic.mp;
      assumption;
    . intro h;
      apply f.atomic.mpr;
      apply g.atomic.mpr;
      assumption;

def bisimulation {M₁ M₂ : Kripke.Model α} (f : M₁ →ₚ M₂) : M₁ ⇄ M₂ := {
  toRel := Function.graph f,
  atomic := by
    intro x₁ x₂ a e; subst e;
    constructor;
    . apply f.atomic.mp;
    . apply f.atomic.mpr;
  forth := by
    simp;
    intro x₁ y₁ rx₁y₁;
    exact f.forth rx₁y₁;
  back := by
    simp;
    intro x₁ x₂ y₂ e rx₂y₂; subst e;
    obtain ⟨y₁, _⟩ := f.back rx₂y₂;
    use y₁;
}

end Model.PseudoEpimorphism

end PseudoEpimorphism



section

def Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w


structure RootedFrame extends Kripke.Frame where
  root : World
  root_rooted : Frame.isRooted _ root
  default := root


variable [DecidableEq α]

open Relation (TransGen ReflTransGen)

def Frame.PointGenerated (F : Kripke.Frame) (r : F.World) : Kripke.Frame where
  World := { w | w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  World_nonempty := ⟨r, by tauto⟩

namespace Frame.PointGenerated

variable {F : Kripke.Frame} {r : F.World}

lemma rel_transitive (F_trans : Transitive F) : Transitive (F.PointGenerated r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ hxy hyz;
  all_goals aesop;

lemma rel_irreflexive (F_irrefl : Irreflexive F) : Irreflexive (F.PointGenerated r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ h;
  all_goals aesop;

lemma rel_universal (F_refl : Reflexive F) (F_eucl : Euclidean F) : Universal (F.PointGenerated r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl F_eucl;
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply F_refl;
  . exact hy;
  . exact F_symm hx;
  . apply F_symm $ F_eucl hx hy;

lemma rooted : (F.PointGenerated r).isRooted ⟨r, by tauto⟩ := by
  rintro ⟨x, (rfl | hx)⟩;
  . intro h; contradiction;
  . intro _; exact hx;

instance [Finite F.World] : Finite (F.PointGenerated r).World := by
  simp [Frame.PointGenerated];
  apply Subtype.finite;

instance [DecidableEq F.World] : DecidableEq (F.PointGenerated r).World := by
  apply Subtype.instDecidableEq (φ := λ w => w = r ∨ r ≺ w);

end Frame.PointGenerated


abbrev Frame.PointGenerated' (F : Kripke.Frame) (r : F.World) : Kripke.RootedFrame :=
  letI G := F.PointGenerated r;
  {
    World := G.World
    Rel := G.Rel
    root := ⟨r, by tauto⟩
    root_rooted := by simpa using @Frame.PointGenerated.rooted F r
  }
infix:100 "↾" => Frame.PointGenerated'

lemma Frame.PointGenerated'.rel_transitive {F : Kripke.Frame} {r : F.World} : Transitive F → Transitive (F↾r).Rel := PointGenerated.rel_transitive

lemma Frame.PointGenerated'.rel_irreflexive {F : Kripke.Frame} {r : F.World} : Irreflexive F → Irreflexive (F↾r).Rel := PointGenerated.rel_irreflexive


def Model.PointGenerated (M : Kripke.Model α) (r : M.World) : Kripke.Model α where
  Frame := (M.Frame↾r).toFrame
  Valuation w a := M.Valuation w.1 a
infix:100 "↾" => Model.PointGenerated

def Model.PointGenerated.bisimulation (M : Model α) (M_trans : Transitive M.Frame) (r : M.World) : (M↾r) ⇄ M where
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

lemma Model.PointGenerated.bisimulation.rooted (M_trans : Transitive M.Frame := by assumption) : (bisimulation M M_trans r) ⟨r, by simp⟩ r := by simp [bisimulation];

end


section Generation

structure Frame.GeneratedSub (F₁ F₂ : Kripke.Frame) extends F₁ →ₚ F₂ where
 monic : Function.Injective toFun

infix:80 " ⊆ₚ " => Frame.GeneratedSub

end Generation



namespace Frame

variable {F : Kripke.Frame} (x : F.World)

def successors := { w | x ≺^* w }
postfix:100 "↑*" => Frame.upward

def immediate_successors := { w | x ≺ w }
postfix:100 "↑¹" => Frame.immediate_successor

def proper_immediate_successors := { w | x ≠ w ∧ x ≺ w }
postfix:100 "↑" => Frame.proper_immediate_successor


def predeccsors := { w | w ≺^* x }
postfix:100 "↓*" => Frame.downward

def immediate_predeccsors := { w | w ≺ x }
postfix:100 "↓¹" => Frame.immediate_predeccsor

def proper_immediate_predeccsors := { w | w ≠ x ∧ w ≺ x }
postfix:100 "↓" => Frame.proper_immediate_predeccsors

end Frame

end LO.Kripke

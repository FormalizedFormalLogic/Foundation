import Foundation.Modal.Kripke2.Closure

namespace LO.Modal

namespace Kripke

open Formula.Kripke

section Bisimulation

structure Model.Bisimulation (M₁ M₂ : Kripke.Model) where
  toRel : Rel M₁.World M₂.World
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : ℕ} : toRel x₁ x₂ → ((M₁ x₁ a) ↔ (M₂ x₂ a))
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ " => Model.Bisimulation

instance : CoeFun (Model.Bisimulation M₁ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨λ bi => bi.toRel⟩

end Bisimulation


section ModalEquivalent

def ModalEquivalent {M₁ M₂ : Model} (w₁ : M₁.World) (w₂ : M₂.World) : Prop := ∀ {φ}, w₁ ⊧ φ ↔ w₂ ⊧ φ
infix:50 " ↭ " => ModalEquivalent

lemma modal_equivalent_of_bisimilar (Bi : M₁ ⇄ M₂) (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro φ;
  induction φ using Formula.rec' generalizing x₁ x₂ with
  | hatom a => exact Bi.atomic bisx;
  | himp φ ψ ihp ihq =>
    constructor;
    . intro hpq hp;
      exact ihq bisx |>.mp $ hpq $ ihp bisx |>.mpr hp;
    . intro hpq hp;
      exact ihq bisx |>.mpr $ hpq $ ihp bisx |>.mp hp;
  | hbox φ ih =>
    constructor;
    . intro h y₂ rx₂y₂;
      obtain ⟨y₁, ⟨bisy, rx₁y₁⟩⟩ := Bi.back bisx rx₂y₂;
      exact ih bisy |>.mp (h _ rx₁y₁);
    . intro h y₁ rx₁y₁;
      obtain ⟨y₂, ⟨bisy, rx₂y₂⟩⟩ := Bi.forth bisx rx₁y₁;
      exact ih bisy |>.mpr (h _ rx₂y₂);
  | _ => simp_all;

end ModalEquivalent


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
    intro x y hxy;
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
    obtain ⟨y, ⟨rfl, hxy⟩⟩ := g.back hxw;
    obtain ⟨u, ⟨rfl, hfu⟩⟩ := f.back hxy;
    use u;
    constructor;
    . simp_all;
    . assumption;

end Frame.PseudoEpimorphism


structure Model.PseudoEpimorphism (M₁ M₂ : Kripke.Model) extends M₁.toFrame →ₚ M₂.toFrame where
  atomic {w : M₁.World} : (M₁ w a) ↔ (M₂ (toFun w) a)

infix:80 " →ₚ " => Model.PseudoEpimorphism

instance : CoeFun (Model.PseudoEpimorphism M₁ M₂) (λ _ => M₁.World → M₂.World) := ⟨λ f => f.toFun⟩

namespace Model.PseudoEpimorphism

variable {M M₁ M₂ M₃ : Kripke.Model}

def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp;
  back := by simp;
  atomic := by simp;

def ofAtomic (f : M₁.toFrame →ₚ M₂.toFrame) (atomic : ∀ {w a}, (M₁ w a) ↔ (M₂ (f w) a)) : M₁ →ₚ M₂ where
  toFun := f
  forth := f.forth
  back := f.back
  atomic := atomic

def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ := ofAtomic (f.toPseudoEpimorphism.comp (g.toPseudoEpimorphism)) $ by
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

def bisimulation (f : M₁ →ₚ M₂) : M₁ ⇄ M₂ where
  toRel := Function.graph f
  atomic := by
    rintro x₁ x₂ a rfl;
    constructor;
    . apply f.atomic.mp;
    . apply f.atomic.mpr;
  forth := by
    simp only [Function.graph_def, exists_eq_left', forall_eq'];
    intro x₁ y₁ rx₁y₁;
    exact f.forth rx₁y₁;
  back := by
    simp only [Function.graph_def];
    rintro x₁ x₂ y₂ rfl rx₂y₂;
    obtain ⟨y₁, ⟨rfl, _⟩⟩ := f.back rx₂y₂;
    use y₁;

lemma modal_equivalence (f : M₁ →ₚ M₂) (w : M₁.World) : w ↭ (f w) := by
  apply modal_equivalent_of_bisimilar $ Model.PseudoEpimorphism.bisimulation f;
  simp [Model.PseudoEpimorphism.bisimulation];

end Model.PseudoEpimorphism


variable {F₁ F₂ : Kripke.Frame} {M₁ M₂ : Kripke.Model}

lemma validOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁ ⊧ φ → F₂ ⊧ φ := by
  contrapose;
  intro h;
  obtain ⟨V₂, w₂, h⟩ := ValidOnFrame.exists_valuation_world_of_not h;
  obtain ⟨w₁, rfl⟩ := f_surjective w₂;

  apply ValidOnFrame.not_of_exists_valuation_world;
  let V₁ := λ w a => V₂ (f w) a;
  use V₁, w₁;

  exact Model.PseudoEpimorphism.modal_equivalence (M₁ := ⟨F₁, V₁⟩) (M₂ := ⟨F₂, V₂⟩) {
    toFun := f,
    forth := f.forth,
    back := f.back,
    atomic := by aesop;
  } w₁ |>.not.mpr h;

lemma theory_ValidOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁ ⊧* T → F₂ ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h φ hp;
  exact validOnFrame_of_surjective_pseudoMorphism f f_surjective (h hp);

end PseudoEpimorphism


def Frame.isRooted (F : Frame) (r : F.World) : Prop := ∀ w ≠ r, r ≺ w

structure RootedFrame extends Kripke.Frame where
  root : World
  root_rooted : Frame.isRooted _ root
  default := root


section PointGenerated

def Frame.PointGenerated (F : Kripke.Frame) (r : F.World) : Kripke.RootedFrame where
  World := { w | w = r ∨ r ≺ w }
  Rel x y := x.1 ≺ y.1
  world_nonempty := ⟨r, by tauto⟩
  root := ⟨r, by tauto⟩
  root_rooted := by
    rintro ⟨x, (rfl | hx)⟩;
    . intro h; contradiction;
    . intro _; exact hx;
infix:100 "↾" => Frame.PointGenerated

namespace Frame.PointGenerated

variable {F : Kripke.Frame} {r : F.World}

lemma rel_transitive (F_trans : Transitive F) : Transitive (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ ⟨z, (rfl | hz)⟩ hxy hyz;
  all_goals aesop;

lemma rel_irreflexive (F_irrefl : Irreflexive F) : Irreflexive (F↾r).Rel := by
  rintro ⟨x, (rfl | hx)⟩ h;
  all_goals aesop;

lemma rel_universal (F_refl : Reflexive F) (F_eucl : Euclidean F) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl F_eucl;
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  . apply F_refl;
  . exact hy;
  . exact F_symm hx;
  . apply F_symm $ F_eucl hx hy;

instance [Finite F.World] : Finite (F↾r).World := by
  unfold Frame.PointGenerated;
  apply Subtype.finite;

instance [DecidableEq F.World] : DecidableEq (F↾r).World := by
  apply Subtype.instDecidableEq (p := λ w => w = r ∨ r ≺ w);

end Frame.PointGenerated


structure RootedModel extends Kripke.Model, Kripke.RootedFrame where


def Model.PointGenerated (M : Kripke.Model) (r : M.World) : Kripke.RootedModel :=
  letI rF := M.toFrame↾r;
  {
    toFrame := rF.toFrame
    Val := λ w a => M.Val w.1 a
    root := rF |>.root
    root_rooted := rF.root_rooted
  }
infix:100 "↾" => Model.PointGenerated

namespace Model.PointGenerated

variable {M : Kripke.Model}

def bisimulation_of_trans (M_trans : Transitive M.Rel) (r : M.World) : (M↾r).toModel ⇄ M where
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

lemma modal_equivalent_at_root (M_trans : Transitive M.toFrame) (r : M.World) : ModalEquivalent (M₁ := (M↾r).toModel) (M₂ := M) ⟨r, by simp⟩ r
  := modal_equivalent_of_bisimilar (bisimulation_of_trans M_trans r) $ by simp [bisimulation_of_trans];

end Model.PointGenerated

end PointGenerated


section Generation

structure Frame.GeneratedSub (F₁ F₂ : Kripke.Frame) extends F₁ →ₚ F₂ where
 monic : Function.Injective toFun

infix:80 " ⊆ₚ " => Frame.GeneratedSub

end Generation


/-
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
-/


end Kripke

end LO.Modal

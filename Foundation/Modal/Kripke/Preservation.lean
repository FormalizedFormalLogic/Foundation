import Foundation.Modal.Kripke.Closure

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

def Model.Bisimulation.symm (bi : M₁ ⇄ M₂) : M₂ ⇄ M₁ := {
  toRel := λ a b => bi.toRel b a
  atomic := by
    intro x₂ x₁ a h;
    exact (bi.atomic h).symm;
  forth := by
    intro x₂ y₂ x₁ hxy h;
    obtain ⟨y₁, ⟨hy₁, hxy⟩⟩ := bi.back hxy h;
    use y₁;
  back := by
    intro x₁ x₂ y₁ hxy h;
    obtain ⟨y₂, ⟨hy₂, hxy⟩⟩ := bi.forth hxy h;
    use y₂;
}

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

def ModalEquivalent.symm {M₁ M₂ : Model} {w₁ : M₁.World} {w₂ : M₂.World} (h : w₁ ↭ w₂) : w₂ ↭ w₁ := fun {_} => Iff.symm h

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


variable {F₁ F₂ : Kripke.Frame} {M₁ M₂ : Kripke.Model} {φ : Formula ℕ} {T : FormulaSet ℕ}

lemma validOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁ ⊧ φ → F₂ ⊧ φ := by
  intro h V₂ u;
  obtain ⟨x, rfl⟩ := f_surjective u;
  refine (Model.PseudoEpimorphism.ofAtomic (M₁ := ⟨F₁, λ w a => V₂ (f w) a⟩) (M₂ := ⟨F₂, V₂⟩) f ?_).modal_equivalence x |>.mp $ h _ x;
  simp;

lemma theory_ValidOnFrame_of_surjective_pseudoMorphism (f : F₁ →ₚ F₂) (f_surjective : Function.Surjective f) : F₁ ⊧* T → F₂ ⊧* T := by
  simp only [Semantics.realizeSet_iff];
  intro h φ hp;
  exact validOnFrame_of_surjective_pseudoMorphism f f_surjective (h hp);

end PseudoEpimorphism


section Generation

structure Frame.GeneratedSub (F₁ F₂ : Kripke.Frame) extends F₁ →ₚ F₂ where
 monic : Function.Injective toFun
infix:80 " ⥹ " => Frame.GeneratedSub

namespace Frame.GeneratedSub

variable {F₁ F₂ : Kripke.Frame}

end Frame.GeneratedSub


structure Model.GeneratedSub (M₁ M₂ : Kripke.Model) extends M₁.toFrame ⥹ M₂.toFrame where
  atomic : ∀ a, ∀ w, (M₁ w a) ↔ (M₂ (toFun w) a)
infix:80 " ⥹ " => Model.GeneratedSub

namespace Model.GeneratedSub

variable {M₁ M₂ : Kripke.Model}

def ofAtomic (g : M₁.toFrame ⥹ M₂.toFrame) (atomic : ∀ a w, M₁ w a ↔ M₂ (g.toFun w) a) : M₁ ⥹ M₂ where
  toFun := g.toFun
  forth := g.forth
  back := g.back
  monic := g.monic
  atomic := atomic

variable (g : M₁ ⥹ M₂)

def pMorphism : M₁ →ₚ M₂ where
  toFun := g.toFun
  forth := g.forth
  back := g.back
  atomic := fun {a w} => (g.atomic a w)

def bisimulation : M₁ ⇄ M₂ := Model.PseudoEpimorphism.bisimulation g.pMorphism

def modal_equivalence (w : M₁.World) : w ↭ (g.toFun w) := Model.PseudoEpimorphism.modal_equivalence g.pMorphism w

end Model.GeneratedSub

variable {F₁ F₂ : Kripke.Frame} {M₁ M₂ : Kripke.Model} {φ : Formula ℕ} {T : FormulaSet ℕ}

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

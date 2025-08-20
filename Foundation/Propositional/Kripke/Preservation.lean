import Foundation.Propositional.Kripke.Basic

namespace LO.Propositional

namespace Kripke

open Formula.Kripke

section Bisimulation

structure Model.Bisimulation (M₁ M₂ : Kripke.Model) where
  toRel : M₁.World → M₂.World → Prop
  atomic {x₁ : M₁.World} {x₂ : M₂.World} {a : ℕ} : toRel x₁ x₂ → ((M₁ x₁ a) ↔ (M₂ x₂ a))
  forth {x₁ y₁ : M₁.World} {x₂ : M₂.World} : toRel x₁ x₂ → x₁ ≺ y₁ → ∃ y₂ : M₂.World, toRel y₁ y₂ ∧ x₂ ≺ y₂
  back {x₁ : M₁.World} {x₂ y₂ : M₂.World} : toRel x₁ x₂ → x₂ ≺ y₂ → ∃ y₁ : M₁.World, toRel y₁ y₂ ∧ x₁ ≺ y₁

infix:80 " ⇄ " => Model.Bisimulation

instance : CoeFun (Model.Bisimulation M₁ M₂) (λ _ => M₁.World → M₂.World → Prop) := ⟨λ bi => bi.toRel⟩

def Model.Bisimulation.symm (bi : M₁ ⇄ M₂) : M₂ ⇄ M₁ := {
  toRel := λ a b => bi.toRel b a
  atomic := by
    intro x₂ x₁ a h
    exact (bi.atomic h).symm
  forth := by
    intro x₂ y₂ x₁ hxy h
    obtain ⟨y₁, ⟨hy₁, hxy⟩⟩ := bi.back hxy h
    use y₁
  back := by
    intro x₁ x₂ y₁ hxy h
    obtain ⟨y₂, ⟨hy₂, hxy⟩⟩ := bi.forth hxy h
    use y₂
}

end Bisimulation


section ModalEquivalent

def ModalEquivalent {M₁ M₂ : Model} (w₁ : M₁.World) (w₂ : M₂.World) : Prop := ∀ {φ}, w₁ ⊧ φ ↔ w₂ ⊧ φ
infix:50 " ↭ " => ModalEquivalent

lemma modal_equivalent_of_bisimilar (Bi : M₁ ⇄ M₂) (bisx : Bi x₁ x₂) : x₁ ↭ x₂ := by
  intro φ
  induction φ generalizing x₁ x₂ with
  | hatom a => exact Bi.atomic bisx
  | hand φ ψ ihφ ihψ =>
    constructor
    . rintro ⟨hφ, hψ⟩
      constructor
      . exact ihφ bisx |>.mp hφ
      . exact ihψ bisx |>.mp hψ
    . rintro ⟨hφ, hψ⟩
      constructor
      . exact ihφ bisx |>.mpr hφ
      . exact ihψ bisx |>.mpr hψ
  | hor φ ψ ihφ ihψ =>
    constructor
    . rintro (hφ | hψ)
      . left;  exact ihφ bisx |>.mp hφ
      . right; exact ihψ bisx |>.mp hψ
    . rintro (hφ | hψ)
      . left;  exact ihφ bisx |>.mpr hφ
      . right; exact ihψ bisx |>.mpr hψ
  | himp φ ψ ihφ ihψ =>
    constructor
    . rintro hφψ y₂ Rx₂y₂ hφ
      obtain ⟨y₁, ⟨bisy, Rx₁y₁⟩⟩ := Bi.back bisx Rx₂y₂
      exact ihψ bisy |>.mp $ hφψ Rx₁y₁ ((ihφ bisy).mpr hφ)
    . rintro hφψ y₁ Rx₁y₁ hφ
      obtain ⟨y₂, ⟨bisy, Rx₂y₂⟩⟩ := Bi.forth bisx Rx₁y₁
      exact ihψ bisy |>.mpr $ hφψ Rx₂y₂ ((ihφ bisy).mp hφ)
  | _ => simp_all

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
  forth := by simp
  back := by simp

def comp (f : F₁ →ₚ F₂) (g : F₂ →ₚ F₃) : F₁ →ₚ F₃ where
  toFun := g ∘ f
  forth := by
    intro x y hxy
    exact g.forth $ f.forth hxy
  back := by
    intro x w hxw
    obtain ⟨y, ⟨rfl, hxy⟩⟩ := g.back hxw
    obtain ⟨u, ⟨rfl, hfu⟩⟩ := f.back hxy
    use u
    constructor
    . simp_all
    . assumption

end Frame.PseudoEpimorphism


structure Model.PseudoEpimorphism (M₁ M₂ : Kripke.Model) extends M₁.toFrame →ₚ M₂.toFrame where
  atomic {w : M₁.World} : (M₁ w a) ↔ (M₂ (toFun w) a)

infix:80 " →ₚ " => Model.PseudoEpimorphism

instance : CoeFun (Model.PseudoEpimorphism M₁ M₂) (λ _ => M₁.World → M₂.World) := ⟨λ f => f.toFun⟩

namespace Model.PseudoEpimorphism

variable {M M₁ M₂ M₃ : Kripke.Model}

def ofAtomic (f : M₁.toFrame →ₚ M₂.toFrame) (atomic : ∀ {w a}, (M₁ w a) ↔ (M₂ (f w) a)) : M₁ →ₚ M₂ where
  toFun := f
  forth := f.forth
  back := f.back
  atomic := atomic

def id : M →ₚ M where
  toFun := _root_.id
  forth := by simp
  back := by simp
  atomic := by simp

def comp (f : M₁ →ₚ M₂) (g : M₂ →ₚ M₃) : M₁ →ₚ M₃ := ofAtomic (f.toPseudoEpimorphism.comp (g.toPseudoEpimorphism)) $ by
  intro x φ
  constructor
  . intro h
    apply g.atomic.mp
    apply f.atomic.mp
    assumption
  . intro h
    apply f.atomic.mpr
    apply g.atomic.mpr
    assumption

def bisimulation (f : M₁ →ₚ M₂) : M₁ ⇄ M₂ where
  toRel x y := y = f x
  atomic := by
    rintro x₁ x₂ a rfl
    constructor
    . apply f.atomic.mp
    . apply f.atomic.mpr
  forth := by
    simp only [exists_eq_left, forall_eq]
    intro x₁ y₁ rx₁y₁
    exact f.forth rx₁y₁
  back := by
    rintro x₁ x₂ y₂ rfl rx₂y₂
    obtain ⟨y₁, ⟨rfl, _⟩⟩ := f.back rx₂y₂
    use y₁

lemma modal_equivalence (f : M₁ →ₚ M₂) (w : M₁.World) : w ↭ (f w) := by
  apply modal_equivalent_of_bisimilar $ Model.PseudoEpimorphism.bisimulation f
  simp [Model.PseudoEpimorphism.bisimulation]

end Model.PseudoEpimorphism

end PseudoEpimorphism

end Kripke

end LO.Propositional

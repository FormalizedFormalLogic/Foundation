module

public import Foundation.Logic.LogicSymbol

/-! # Forcing relation -/

@[expose] public section

namespace LO

class ForcingRelation (W : Type*) (F : outParam Type*) where
  Forces : W → F → Prop

infix:45 " ⊩ " => ForcingRelation.Forces

class ForcingExists (W : Type*) (α : outParam Type*) where
  Forces : W → α → Prop

infix:45 " ⊩↓ " => ForcingExists.Forces

namespace ForcingRelation

variable {W : Type*} {F : Type*} [ForcingRelation W F] [LogicalConnective F]

abbrev NotForces (w : W) (φ : F) : Prop := ¬w ⊩ φ

infix:45 " ⊮ " => NotForces

variable (W)

class BasicSemantics where
  verum (w : W) : w ⊩ ⊤
  falsum (w : W) : ¬w ⊩ ⊥
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ

class IntKripke (R : outParam (W → W → Prop)) extends BasicSemantics W where
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → ¬v ⊩ φ)
  imply (w : W) : w ⊩ φ ➝ ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)
  monotone {w : W} : w ⊩ φ → ∀ v, R w v → v ⊩ φ

variable {W}

attribute [simp, grind]
  BasicSemantics.verum BasicSemantics.falsum BasicSemantics.and
  BasicSemantics.or IntKripke.imply IntKripke.not

variable (W)

abbrev AllForces (φ : F) : Prop := ∀ w : W, w ⊩ φ

infix:45 " ∀⊩ " => AllForces

abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop := ∀ φ ∈ s, W ∀⊩ φ

infix:45 " ∀⊩* " => AllForcesSet

variable {W}

namespace AllForces

@[simp] lemma verum [BasicSemantics W] : W ∀⊩ ⊤ := fun _ ↦ by simp

@[simp] lemma falsum [BasicSemantics W] [Inhabited W] : ¬W ∀⊩ ⊥ := fun h ↦ by simpa using h default

@[simp] lemma and [BasicSemantics W] : W ∀⊩ φ ⋏ ψ ↔ W ∀⊩ φ ∧ W ∀⊩ ψ := by
  simp [AllForces]; grind

end AllForces

end ForcingRelation

/-! ### Forcing relation for classical logic -/

class WeakForcingRelation (ℙ : Type*) (F : outParam Type*) where
  WeaklyForces : ℙ → F → Prop

infix:45 " ⊩ᶜ " => WeakForcingRelation.WeaklyForces

namespace WeakForcingRelation

variable {ℙ : Type*} {F : Type*} [WeakForcingRelation ℙ F] [LogicalConnective F]

abbrev NotForces (p : ℙ) (φ : F) : Prop := ¬p ⊩ᶜ φ

infix:45 " ⊮ᶜ " => NotForces

variable (ℙ)

class BasicSemantics where
  verum (p : ℙ) : p ⊩ᶜ ⊤
  falsum (p : ℙ) : ¬p ⊩ᶜ ⊥
  and (p : ℙ) : p ⊩ᶜ φ ⋏ ψ ↔ p ⊩ᶜ φ ∧ p ⊩ᶜ ψ

class ClassicalKripke (R : outParam (ℙ → ℙ → Prop)) extends BasicSemantics ℙ where
  or (p : ℙ) : p ⊩ᶜ φ ⋎ ψ ↔ ∀ q, R p q → ∃ x, R q x ∧ (x ⊩ᶜ φ ∨ x ⊩ᶜ ψ)
  not (p : ℙ) : p ⊩ᶜ ∼φ ↔ (∀ q, R p q → ¬q ⊩ᶜ φ)
  imply (p : ℙ) : p ⊩ᶜ φ ➝ ψ ↔ (∀ q, R p q → q ⊩ᶜ φ → q ⊩ᶜ ψ)
  monotone {p : ℙ} : p ⊩ᶜ φ → ∀ q, R p q → q ⊩ᶜ φ
  generic {p : ℙ} : (∀ q, R p q → ∃ r, R q r ∧ r ⊩ᶜ φ) → p ⊩ᶜ φ

variable {ℙ}

attribute [simp, grind]
  BasicSemantics.verum BasicSemantics.falsum BasicSemantics.and
  ClassicalKripke.or ClassicalKripke.imply ClassicalKripke.not

variable (ℙ)

abbrev AllForces (φ : F) : Prop := ∀ p : ℙ, p ⊩ᶜ φ

infix:45 " ∀⊩ᶜ " => AllForces

abbrev AllForcesSet (s : S) [AdjunctiveSet F S] : Prop := ∀ φ ∈ s, ℙ ∀⊩ᶜ φ

infix:45 " ∀⊩ᶜ* " => AllForcesSet

variable {ℙ}

namespace AllForces

@[simp] lemma verum [BasicSemantics ℙ] : ℙ ∀⊩ᶜ ⊤ := fun _ ↦ by simp

@[simp] lemma falsum [BasicSemantics ℙ] [Inhabited ℙ] : ¬ℙ ∀⊩ᶜ ⊥ := fun h ↦ by simpa using h default

@[simp] lemma and [BasicSemantics ℙ] : ℙ ∀⊩ᶜ φ ⋏ ψ ↔ ℙ ∀⊩ᶜ φ ∧ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces]; grind

/-
@[simp] lemma or [ClassicalKripke ℙ R] : ℙ ∀⊩ᶜ φ ⋎ ψ ↔ ℙ ∀⊩ᶜ φ ∨ ℙ ∀⊩ᶜ ψ := by
  simp [AllForces]
  constructor
  · intro h
    by_contra! C
    rcases C with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
-/

end AllForces


end WeakForcingRelation

end LO

end

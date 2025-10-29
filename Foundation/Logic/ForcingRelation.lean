import Foundation.Logic.LogicSymbol

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

class IntKripke (R : outParam (W → W → Prop)) where
  verum (w : W) : w ⊩ ⊤
  falsum (w : W) : w ⊮ ⊥
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → v ⊮ φ)
  imply (w : W) : w ⊩ φ ➝ ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)

variable {W}

attribute [simp, grind]
  IntKripke.verum IntKripke.falsum IntKripke.and
  IntKripke.or IntKripke.imply IntKripke.not
attribute [grind]
  IntKripke.imply IntKripke.not

namespace IntKripke

variable {R : W → W → Prop} [IntKripke W R]

end IntKripke

end ForcingRelation

class WeakForcingRelation (W : Type*) (F : outParam Type*) where
  Forces : W → F → Prop

infix:45 " ⊩ᶜ " => WeakForcingRelation.Forces
namespace WeakForcingRelation

variable {W : Type*} {F : Type*} [WeakForcingRelation W F] [LogicalConnective F]

abbrev NotForces (w : W) (φ : F) : Prop := ¬w ⊩ᶜ φ

infix:45 " ⊮ᶜ " => NotForces

variable (W)

class ClassicalKripke (R : outParam (W → W → Prop)) where
  verum (w : W) : w ⊩ᶜ ⊤
  falsum (w : W) : w ⊮ᶜ ⊥
  and (w : W) : w ⊩ᶜ φ ⋏ ψ ↔ w ⊩ᶜ φ ∧ w ⊩ᶜ ψ
  or (w : W) : w ⊩ᶜ φ ⋎ ψ ↔ ∀ v, R w v → ∃ x, R v x ∧ (x ⊩ᶜ φ ∨ x ⊩ᶜ ψ)
  not (w : W) : w ⊩ᶜ ∼φ ↔ (∀ v, R w v → v ⊮ᶜ φ)
  imply (w : W) : w ⊩ᶜ φ ➝ ψ ↔ (∀ v, R w v → v ⊩ᶜ φ → v ⊩ᶜ ψ)

attribute [simp, grind]
  ClassicalKripke.verum ClassicalKripke.falsum ClassicalKripke.and
  ClassicalKripke.or ClassicalKripke.imply ClassicalKripke.not
attribute [grind]
  ClassicalKripke.imply ClassicalKripke.not

end WeakForcingRelation

end LO

import Foundation.Logic.LogicSymbol

namespace LO

class ForcingRelation (W : Type*) (F : outParam Type*) where
  Forces : W → F → Prop

infix:45 " ⊩ " => ForcingRelation.Forces

namespace ForcingRelation

variable {W : Type*} {F : Type*} [ForcingRelation W F] [LogicalConnective F]

abbrev NotForces (w : W) (φ : F) : Prop := ¬ w ⊩ φ

infix:45 " ⊮ " => NotForces

variable (W)

class Kripke (R : outParam (W → W → Prop)) where
  verum (w : W) : w ⊩ ⊤
  falsum (w : W) : w ⊮ ⊥
  and (w : W) : w ⊩ φ ⋏ ψ ↔ w ⊩ φ ∧ w ⊩ ψ
  or (w : W) : w ⊩ φ ⋎ ψ ↔ w ⊩ φ ∨ w ⊩ ψ
  not (w : W) : w ⊩ ∼φ ↔ (∀ v, R w v → v ⊮ φ)
  implies (w : W) : w ⊩ φ ➝ ψ ↔ (∀ v, R w v → v ⊩ φ → v ⊩ ψ)

attribute [simp] Kripke.verum Kripke.falsum Kripke.and Kripke.or

end ForcingRelation

end LO

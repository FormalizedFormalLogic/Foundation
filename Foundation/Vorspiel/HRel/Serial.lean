import Foundation.Vorspiel.HRel.Basic

variable {α} {R : HRel α}

def Serial (R : HRel α) := ∀ x, ∃ y, R x y
class IsSerial (R : HRel α) where
  serial : Serial R

instance [IsRefl _ R] : IsSerial R := ⟨fun x ↦ ⟨x, IsRefl.refl x⟩⟩

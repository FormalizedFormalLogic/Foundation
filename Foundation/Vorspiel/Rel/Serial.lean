import Foundation.Vorspiel.Rel.Basic

variable {α} {R : Rel α α}

def Serial (R : Rel α α) := ∀ x, ∃ y, R x y
class IsSerial (R : Rel α α) where
  serial : Serial R

instance [IsRefl _ R] : IsSerial R := ⟨fun x ↦ ⟨x, IsRefl.refl x⟩⟩

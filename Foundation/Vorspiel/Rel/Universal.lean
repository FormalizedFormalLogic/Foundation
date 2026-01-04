import Foundation.Vorspiel.Rel.Coreflexive

variable {α} {R : Rel α α}

/-- Everything is related on `R` -/
def Universal (R : Rel α α) := ∀ ⦃x y⦄, R x y

class IsUniversal (R : Rel α α) where
  universal : Universal R

instance [IsUniversal R] : IsRefl α R := ⟨by intro x; apply IsUniversal.universal⟩
instance [IsUniversal R] : IsRightEuclidean R := ⟨by intro x y z _ _; apply IsUniversal.universal⟩

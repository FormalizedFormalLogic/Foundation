import Foundation.Vorspiel.HRel.Coreflexive

variable {α} {R : HRel α}

/-- Everything is related on `R` -/
def Universal (R : HRel α) := ∀ ⦃x y⦄, R x y

class IsUniversal (R : HRel α) where
  universal : Universal R

instance [IsUniversal R] : IsRefl α R := ⟨by intro x; apply IsUniversal.universal⟩
instance [IsUniversal R] : IsRightEuclidean R := ⟨by intro x y z _ _; apply IsUniversal.universal⟩

import Foundation.Vorspiel.HRel.Coreflexive

variable {α} {R : HRel α}

/-- Nothing is related on `R` -/
def Isolated (R : HRel α) := ∀ ⦃x y⦄, ¬R x y

class IsIsolated (R : HRel α) where
  isolated : Isolated R

@[simp] lemma isolated [IsIsolated R] {x y : α} : ¬R x y := by apply IsIsolated.isolated

instance [IsIsolated R] : IsCoreflexive R := ⟨by simp_all [Coreflexive]⟩

instance [IsIsolated R] : IsIrrefl α R := ⟨by simp_all⟩

instance [IsIsolated R] : IsTrans α R := ⟨by simp_all⟩

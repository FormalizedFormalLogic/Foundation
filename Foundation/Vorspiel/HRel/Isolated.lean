import Foundation.Vorspiel.HRel.Coreflexive

variable {α} {R : HRel α}

/-- Nothing is related on `R` -/
def Isolated (R : HRel α) := ∀ ⦃x y⦄, ¬R x y

class IsIsolated (R : HRel α) where
  isolated : Isolated R

instance [IsIsolated R] : IsCoreflexive R := ⟨by
  intro x y Rxy;
  exfalso;
  apply IsIsolated.isolated Rxy;
⟩

instance [IsIsolated R] : IsIrrefl α R := ⟨by
  intro x Rxx;
  apply IsIsolated.isolated Rxx;
⟩

instance [IsIsolated R] : IsTrans α R := ⟨by
  intro x y z Rxy;
  exfalso;
  apply IsIsolated.isolated Rxy;
⟩

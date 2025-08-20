import Foundation.Vorspiel.HRel.Basic

variable {α} {R : HRel α}


def Convergent (R : HRel α) := ∀ ⦃x y⦄, x ≠ y → ∃ u, R x u ∧ R y u

class IsConvergent (R : HRel α) where
  convergent : Convergent R


def StronglyConvergent (R : HRel α) := ∀ ⦃x y⦄, ∃ u, R x u ∧ R y u

/-- NOTE: It is equivalent to `IsDirected` -/
class IsStronglyConvergent (R : HRel α) where
  s_convergent : StronglyConvergent R

instance [IsStronglyConvergent R] : IsConvergent R := ⟨by
  rintro x y _
  apply IsStronglyConvergent.s_convergent
⟩


def PiecewiseConvergent (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → y ≠ z → ∃ u, R y u ∧ R z u

class IsPiecewiseConvergent (R : HRel α) where
  p_convergent : PiecewiseConvergent R


def PiecewiseStronglyConvergent (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → ∃ u, R y u ∧ R z u

class IsPiecewiseStronglyConvergent (R : HRel α) where
  ps_convergent : PiecewiseStronglyConvergent R

instance [IsPiecewiseStronglyConvergent R] : IsPiecewiseConvergent R := ⟨by
  rintro x y z Rxy Rxz _
  apply IsPiecewiseStronglyConvergent.ps_convergent Rxy Rxz
⟩

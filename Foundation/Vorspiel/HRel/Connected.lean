import Foundation.Vorspiel.HRel.Basic

variable {α} {R : HRel α}

def PiecewiseConnected (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ y = z ∨ R z y)

class IsPiecewiseConnected (R : HRel α) where
  p_connected : PiecewiseConnected R

lemma IsPiecewiseConnected.p_connected' {R : HRel α} [IsPiecewiseConnected R] {x y z : α} (Rxy : R x y) (Rxz : R x z) (hyz : y ≠ z) : R y z ∨ R z y := by
  rcases IsPiecewiseConnected.p_connected Rxy Rxz with (Ryz | rfl | Rzy) <;> tauto;

instance [IsTrichotomous _ R] : IsPiecewiseConnected R :=
  ⟨fun ⦃_ y z⦄ _ _ ↦ IsTrichotomous.trichotomous y z⟩


def PiecewiseStronglyConnected (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ R z y)

class IsPiecewiseStronglyConnected (R : HRel α) where
  ps_connected : PiecewiseStronglyConnected R

instance [IsTotal _ R] : IsPiecewiseStronglyConnected R := ⟨fun ⦃_ y z⦄ _ _ ↦ IsTotal.total y z⟩

instance [IsPiecewiseConnected R] [IsRefl _ R] : IsPiecewiseStronglyConnected R := ⟨by
  intro x y z Rxy Rxz;
  rcases IsPiecewiseConnected.p_connected Rxy Rxz with (Ryz | rfl | Rzy);
  . tauto;
  . left; apply refl;
  . tauto;
⟩

instance [IsPiecewiseStronglyConnected R] : IsPiecewiseConnected R := ⟨by
  intro x y z Rxy Rxz;
  rcases IsPiecewiseStronglyConnected.ps_connected Rxy Rxz <;> tauto;
⟩

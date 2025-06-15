import Foundation.Vorspiel.HRel.Basic

variable {α} {R : HRel α}

def PiecewiseConnected (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ y = z ∨ R z y)

class IsPiecewiseConnected (R : HRel α) where
  pconnected : PiecewiseConnected R

instance [IsTrichotomous _ R] : IsPiecewiseConnected R :=
  ⟨fun ⦃_ y z⦄ _ _ ↦ IsTrichotomous.trichotomous y z⟩


def PiecewiseStronglyConnected (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ R z y)

class IsPiecewiseStronglyConnected (R : HRel α) where
  psconnected : PiecewiseStronglyConnected R

instance [IsTotal _ R] : IsPiecewiseStronglyConnected R := ⟨fun ⦃_ y z⦄ _ _ ↦ IsTotal.total y z⟩

instance [IsPiecewiseConnected R] [IsRefl _ R] : IsPiecewiseStronglyConnected R := ⟨by
  intro x y z Rxy Rxz;
  rcases IsPiecewiseConnected.pconnected Rxy Rxz with (Ryz | rfl | Rzy);
  . tauto;
  . left; apply refl;
  . tauto;
⟩

instance [IsPiecewiseStronglyConnected R] : IsPiecewiseConnected R := ⟨by
  intro x y z Rxy Rxz;
  rcases IsPiecewiseStronglyConnected.psconnected Rxy Rxz <;> tauto;
⟩

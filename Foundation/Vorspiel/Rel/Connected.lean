module
import Foundation.Vorspiel.Rel.Euclidean
import Foundation.Vorspiel.Rel.Convergent

variable {α} {R : Rel α α}

def PiecewiseConnected (R : Rel α α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ y = z ∨ R z y)

class IsPiecewiseConnected (R : Rel α α) where
  p_connected : PiecewiseConnected R

lemma IsPiecewiseConnected.p_connected' {R : Rel α α} [IsPiecewiseConnected R] {x y z : α} (Rxy : R x y) (Rxz : R x z) (hyz : y ≠ z) : R y z ∨ R z y := by
  rcases IsPiecewiseConnected.p_connected Rxy Rxz with (Ryz | rfl | Rzy) <;> tauto;

instance [IsTrichotomous _ R] : IsPiecewiseConnected R :=
  ⟨fun ⦃_ y z⦄ _ _ ↦ IsTrichotomous.trichotomous y z⟩

instance [IsRightEuclidean R] : IsPiecewiseConnected R := ⟨by
  intro x y z Rxy Rxz;
  have : R y z := IsRightEuclidean.reucl Rxy Rxz;
  tauto;
⟩

def PiecewiseStronglyConnected (R : Rel α α) := ∀ ⦃x y z⦄, R x y → R x z → (R y z ∨ R z y)

class IsPiecewiseStronglyConnected (R : Rel α α) where
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

instance [IsRefl _ R] [IsPiecewiseStronglyConnected R] : IsPiecewiseStronglyConvergent R := ⟨by
  intro x y z Rxy Rxz;
  rcases IsPiecewiseStronglyConnected.ps_connected Rxy Rxz with (Ryz | Rzy);
  . use z;
    constructor;
    . assumption;
    . apply IsRefl.refl;
  . use y;
    constructor;
    . apply IsRefl.refl;
    . assumption;
⟩

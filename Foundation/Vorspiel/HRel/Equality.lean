import Foundation.Vorspiel.HRel.Coreflexive
import Foundation.Vorspiel.HRel.Connected

variable {α} {R : HRel α}

/-- States that `R` is `=` -/
def Equality (R : HRel α) := ∀ ⦃x y⦄, R x y ↔ x = y

class IsEquality (R : HRel α) where
  equality : Equality R

instance [IsRefl _ R] [IsCoreflexive R] : IsEquality R := ⟨by
  intro x y;
  constructor;
  . apply IsCoreflexive.corefl;
  . rintro rfl; apply IsRefl.refl;
⟩

instance [IsEquality R] : IsRefl α R := ⟨fun x ↦ IsEquality.equality.mpr (Eq.refl x)⟩

instance [IsEquality R] : IsCoreflexive R := ⟨fun _ _ Rxy ↦ IsEquality.equality.1 Rxy⟩

instance [IsEquality R] : IsSymm α R := ⟨by
  intro x y Rxy;
  replace Rxy := IsEquality.equality.1 Rxy; subst Rxy;
  apply IsRefl.refl;
⟩

instance [IsEquality R] : IsAntisymm α R := ⟨by
  intro x y Rxy Ryx;
  replace Rxy := IsEquality.equality.1 Rxy;
  replace Ryx := IsEquality.equality.1 Ryx;
  tauto;
⟩

instance [IsEquality R] : IsTrans α R := ⟨by
  rintro x y z Rxy Ryz;
  replace Rxy := IsEquality.equality.1 Rxy;
  replace Ryz := IsEquality.equality.1 Ryz;
  subst Rxy Ryz;
  apply refl;
⟩

instance [IsEquality R] : IsPiecewiseStronglyConnected R := ⟨by
  rintro x y z Rxy Rxz;
  replace Rxy := IsEquality.equality.1 Rxy;
  replace Rxz := IsEquality.equality.1 Rxz;
  subst Rxy Rxz;
  left;
  apply refl;
⟩

instance : IsEquality (α := α) (· = ·) := ⟨by intro x y; simp [Equality]⟩

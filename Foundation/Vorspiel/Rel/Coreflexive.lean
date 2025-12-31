import Foundation.Vorspiel.Rel.Euclidean

variable {α} {R : Rel α α}

def Coreflexive (R : Rel α α) := ∀ ⦃x y⦄, R x y → x = y

class IsCoreflexive (R : Rel α α) where
  corefl : Coreflexive R

instance [IsSymm _ R] [IsAntisymm _ R] : IsCoreflexive R := ⟨by
  intro x y Rxy;
  apply IsAntisymm.antisymm (r := R);
  . assumption;
  . exact IsSymm.symm _ _ Rxy;
⟩

instance [IsCoreflexive R] : IsTrans _ R := ⟨by
  rintro x y z Rxy Ryz;
  rwa [IsCoreflexive.corefl Rxy, IsCoreflexive.corefl Ryz] at *;
⟩

instance [IsCoreflexive R] : IsSymm _ R := ⟨by
  intro x y Rxy;
  rwa [IsCoreflexive.corefl Rxy] at *;
⟩

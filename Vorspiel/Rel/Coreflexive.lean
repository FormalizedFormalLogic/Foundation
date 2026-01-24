module

public import Vorspiel.Rel.Basic

@[expose]
public section

open Std

variable {α} {R : Rel α α}

def Coreflexive (R : Rel α α) := ∀ ⦃x y⦄, R x y → x = y
class IsCoreflexive (R : Rel α α) where corefl : Coreflexive R

instance [Symm R] [IsAntisymm _ R] : IsCoreflexive R := ⟨by
  intro x y Rxy;
  apply IsAntisymm.antisymm _ _ Rxy;
  exact Symm.symm _ _ Rxy;
⟩

instance [IsCoreflexive R] : IsTrans _ R := ⟨by
  rintro x y z Rxy Ryz;
  rwa [IsCoreflexive.corefl Rxy, IsCoreflexive.corefl Ryz] at *;
⟩

instance [IsCoreflexive R] : Symm R := ⟨by
  intro x y Rxy;
  rwa [IsCoreflexive.corefl Rxy] at *;
⟩

instance : IsCoreflexive (α := α) (· = ·) := ⟨by tauto⟩

end

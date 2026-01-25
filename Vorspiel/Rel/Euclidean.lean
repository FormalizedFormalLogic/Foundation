module

public import Vorspiel.Rel.Serial

@[expose]
public section

open Std

variable {α} {R : Rel α α}

def RightEuclidean (R : Rel α α) := ∀ ⦃x y z⦄, R x y → R x z → R y z
class IsRightEuclidean (R : Rel α α) where reucl : RightEuclidean R

instance [Symm R] [IsTrans _ R] : IsRightEuclidean R := ⟨by
  intro x y z Rxy Rxz;
  apply Symm.symm;
  apply IsTrans.trans;
  . exact Symm.symm _ _ Rxz;
  . assumption;
⟩

instance [IsRefl _ R] [IsRightEuclidean R] : Symm R := ⟨by
  intro x y Rxy;
  exact IsRightEuclidean.reucl Rxy $ IsRefl.refl x
⟩

instance [Symm R] [IsRightEuclidean R] : IsTrans α R := ⟨by
  intro x y z Rxy Ryz;
  apply Symm.symm;
  apply IsRightEuclidean.reucl;
  . exact Ryz;
  . exact Symm.symm _ _ Rxy;
⟩

instance [IsRefl _ R] [IsRightEuclidean R] : IsTrans α R := inferInstance


def LeftEuclidean (R : Rel α α) := ∀ ⦃x y z⦄, R y x → R z x → R y z
class IsLeftEuclidean (R : Rel α α) where leucl : LeftEuclidean R


end

import Foundation.Vorspiel.Rel.Serial

variable {α} {R : Rel α α}

def RightEuclidean (R : Rel α α) := ∀ ⦃x y z⦄, R x y → R x z → R y z

class IsRightEuclidean (R : Rel α α) where
  reucl : RightEuclidean R

lemma IsRightEuclidean.reucl' [IsRightEuclidean R] {x y z : α} (Rxy : R x y) (Rxz : R x z) : R z y := reucl Rxz Rxy

instance [Std.Symm R] [IsTrans _ R] : IsRightEuclidean R := ⟨by
  intro x y z Rxy Rxz;
  apply Std.Symm.symm;
  apply IsTrans.trans;
  . exact Std.Symm.symm _ _ Rxz;
  . assumption;
⟩


instance [IsRefl _ R] [IsRightEuclidean R] : Std.Symm R := ⟨by
  intro x y Rxy;
  apply IsRightEuclidean.reucl Rxy;
  . apply IsRefl.refl
⟩

instance [Std.Symm R] [IsRightEuclidean R] : IsTrans α R := ⟨by
  intro x y z Rxy Ryz;
  apply Std.Symm.symm;
  apply IsRightEuclidean.reucl;
  . exact Ryz;
  . exact Std.Symm.symm _ _ Rxy;
⟩

instance [IsRefl _ R] [IsRightEuclidean R] : IsTrans α R := inferInstance

instance [Std.Symm R] [IsTrans _ R] [IsSerial R] : IsRefl α R := ⟨by
  rintro x;
  obtain ⟨y, Rxy⟩ := IsSerial.serial (R := R) x;
  apply IsTrans.trans;
  . exact Rxy;
  . apply Std.Symm.symm; exact Rxy;
⟩


def LeftEuclidean (R : Rel α α) := ∀ ⦃x y z⦄, R y x → R z x → R y z

class IsLeftEuclidean (R : Rel α α) where
  leucl : LeftEuclidean R

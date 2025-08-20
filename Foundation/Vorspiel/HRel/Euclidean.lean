import Foundation.Vorspiel.HRel.Serial

variable {α} {R : HRel α}

def RightEuclidean (R : HRel α) := ∀ ⦃x y z⦄, R x y → R x z → R y z

class IsRightEuclidean (R : HRel α) where
  reucl : RightEuclidean R

lemma IsRightEuclidean.reucl' [IsRightEuclidean R] {x y z : α} (Rxy : R x y) (Rxz : R x z) : R z y := reucl Rxz Rxy

instance [IsSymm _ R] [IsTrans _ R] : IsRightEuclidean R := ⟨by
  intro x y z Rxy Rxz
  apply IsSymm.symm
  apply IsTrans.trans
  . exact IsSymm.symm _ _ Rxz
  . assumption
⟩


instance [IsRefl _ R] [IsRightEuclidean R] : IsSymm α R := ⟨by
  intro x y Rxy
  apply IsRightEuclidean.reucl Rxy
  . apply IsRefl.refl
⟩

instance [IsSymm _ R] [IsRightEuclidean R] : IsTrans α R := ⟨by
  intro x y z Rxy Ryz
  apply IsSymm.symm
  apply IsRightEuclidean.reucl
  . exact Ryz
  . exact IsSymm.symm _ _ Rxy
⟩

instance [IsRefl _ R] [IsRightEuclidean R] : IsTrans α R := inferInstance

instance [IsSymm _ R] [IsTrans _ R] [IsSerial R] : IsRefl α R := ⟨by
  rintro x
  obtain ⟨y, Rxy⟩ := IsSerial.serial (R := R) x
  apply IsTrans.trans
  . exact Rxy
  . apply IsSymm.symm; exact Rxy
⟩


def LeftEuclidean (R : HRel α) := ∀ ⦃x y z⦄, R y x → R z x → R y z

class IsLeftEuclidean (R : HRel α) where
  leucl : LeftEuclidean R

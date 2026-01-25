module

public import Vorspiel.Rel.Coreflexive
public import Vorspiel.Rel.Connected

@[expose]
public section

open Std

variable {α} {R : Rel α α}

class IsEquality (R : Rel α α) extends IsRefl α R, IsCoreflexive R

lemma equality [IsEquality R] : ∀ ⦃x y⦄, R x y ↔ x = y := by
  intro x y;
  constructor;
  . apply IsCoreflexive.corefl;
  . rintro rfl; apply IsRefl.refl;

instance [IsEquality R] : Std.Symm R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : IsAntisymm α R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : IsTrans α R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : IsPiecewiseStronglyConnected R := ⟨by simp_all [PiecewiseStronglyConnected, equality]⟩


instance : IsEquality (α := α) (· = ·) where

end

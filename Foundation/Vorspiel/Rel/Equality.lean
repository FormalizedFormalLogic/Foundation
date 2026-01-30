module

public import Foundation.Vorspiel.Rel.Coreflexive
public import Foundation.Vorspiel.Rel.Connected

@[expose]
public section

open Std

variable {α} {R : Rel α α}

class IsEquality (R : Rel α α) extends Std.Refl R, IsCoreflexive R

lemma equality [IsEquality R] : ∀ ⦃x y⦄, R x y ↔ x = y := by
  intro x y;
  constructor;
  . apply IsCoreflexive.corefl;
  . rintro rfl; apply Std.Refl.refl;

instance [IsEquality R] : Std.Symm R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : Std.Antisymm R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : IsTrans α R := ⟨by simp_all [equality]⟩
instance [IsEquality R] : IsPiecewiseStronglyConnected R := ⟨by simp_all [PiecewiseStronglyConnected, equality]⟩


instance : IsEquality (α := α) (· = ·) where

end

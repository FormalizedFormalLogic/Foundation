module
import Foundation.Vorspiel.Rel.Coreflexive
import Foundation.Vorspiel.Rel.Connected

variable {α} {R : Rel α α}

class IsEquality (R : Rel α α) extends IsRefl α R, IsCoreflexive R

@[simp]
lemma equality [IsEquality R] : ∀ ⦃x y⦄, R x y ↔ x = y := by
  intro x y;
  constructor;
  . apply IsCoreflexive.corefl;
  . rintro rfl; apply IsRefl.refl;

instance [IsEquality R] : Std.Symm R := ⟨by simp_all⟩

instance [IsEquality R] : IsAntisymm α R := ⟨by simp_all⟩

instance [IsEquality R] : IsTrans α R := ⟨by simp_all⟩

instance [IsEquality R] : IsPiecewiseStronglyConnected R := ⟨by simp_all [PiecewiseStronglyConnected]⟩

instance : IsEquality (α := α) (· = ·) where
  refl := by simp
  corefl := by simp [Coreflexive]

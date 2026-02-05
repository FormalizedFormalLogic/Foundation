module

public import Foundation.Vorspiel.Rel.Basic

@[expose]
public section

open Std

variable {α} {R : Rel α α}

def Serial (R : Rel α α) := ∀ x, ∃ y, R x y
class IsSerial (R : Rel α α) where serial : Serial R

instance [Std.Refl R] : IsSerial R := ⟨fun x ↦ ⟨x, Std.Refl.refl x⟩⟩

instance [Symm R] [IsTrans _ R] [IsSerial R] : Std.Refl R := ⟨by
  rintro x;
  obtain ⟨y, Rxy⟩ := IsSerial.serial (R := R) x;
  apply IsTrans.trans;
  . exact Rxy;
  . apply Symm.symm; exact Rxy;
⟩

end

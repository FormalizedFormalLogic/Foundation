module

public import Foundation.ProvabilityLogic.Kripke.RootedModel

/-!
# Cones
-/

@[expose] public section

namespace FFL.ProvabilityLogic.Kripke

open Model Model.World

variable {κ α : Type*} [Nonempty κ]

namespace Model

variable {M : Model κ α} {r x : M.World} {A : Formula α}

instance : Nonempty { x : M.World // x = r ∨ r ≺ x } := ⟨⟨r, .inl rfl⟩⟩

def cone (M : Model κ α) (r : M.World) : RootedModel { x : M.World // x = r ∨ r ≺ x } α where
  Rel' x y := x.1 ≺ y.1
  Val' x a := M x.1 a
  root := ⟨r, .inl rfl⟩
  root_rel := by
    rintro ⟨x, rfl | h⟩ hx;
    · exact absurd rfl hx;
    · exact h;

instance [M.IsFiniteGL] : (M.cone r).IsFiniteGL where
  trans _ _ _ h₁ h₂ := IsTrans.trans (r := M.Rel) _ _ _ h₁ h₂
  irrefl x := Std.Irrefl.irrefl (r := M.Rel) x.1
  finite := Subtype.finite

instance [M.IsFiniteGrz] : (M.cone r).IsFiniteGrz where
  refl x := Std.Refl.refl (r := M.Rel) x.1
  trans _ _ _ h₁ h₂ := IsTrans.trans (r := M.Rel) _ _ _ h₁ h₂
  antisymm x y h₁ h₂ := Subtype.ext <| Std.Antisymm.antisymm (r := M.Rel) x.1 y.1 h₁ h₂
  finite := Subtype.finite

lemma forces_cone [IsTrans _ M.Rel] {x : (M.cone r).World} : x ⊩ A ↔ x.1 ⊩[M] A := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    obtain ⟨x, hx⟩ := x;
    constructor;
    · intro h y Rxy;
      have hy : y = r ∨ r ≺ y := by
        right;
        rcases hx with rfl | hx;
        exacts [Rxy, IsTrans.trans _ _ _ hx Rxy];
      exact ih.mp (h ⟨y, hy⟩ Rxy);
    · exact fun h y Rxy ↦ ih.mpr (h y.1 Rxy);

end Model

end FFL.ProvabilityLogic.Kripke

end

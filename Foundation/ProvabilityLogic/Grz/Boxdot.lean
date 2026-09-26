module

public import Foundation.ProvabilityLogic.Grz.Basic
public import Foundation.ProvabilityLogic.S.Boxdot

/-!
# The boxdot translation of `Grz` into `GL` and `S`

## References

- [Gol78]
- [Boo80]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment Kripke Kripke.Model Kripke.Model.World

namespace Kripke.Model

variable {κ α : Type*} [Nonempty κ] {M : Model κ α} {A : Formula α}

def irreflGen (M : Model κ α) : Model κ α where
  Rel' := Rel.IrreflGen M.Rel
  Val' := M.Val

instance [M.IsFiniteGrz] : M.irreflGen.IsFiniteGL where
  trans x y z h₁ h₂ := IsTrans.trans (r := Rel.IrreflGen M.Rel) x y z h₁ h₂
  irrefl _ h := h.2 rfl
  finite := IsFiniteGrz.finite (M := M)

def reflGen (M : Model κ α) : Model κ α where
  Rel' x y := x = y ∨ M.Rel x y
  Val' := M.Val

instance [M.IsFiniteGL] : M.reflGen.IsFiniteGrz where
  refl _ := .inl rfl
  trans _ _ _ := by grind [reflGen, IsTrans.trans (r := M.Rel)]
  antisymm _ _ := by grind [reflGen, Std.Irrefl.irrefl (r := M.Rel), IsTrans.trans (r := M.Rel)]
  finite := IsFiniteGL.finite (M := M)

lemma forces_irreflGen_boxdotTranslate [Std.Refl M.Rel] {x : M.World} :
    x ⊩[M.irreflGen] Aᵇ ↔ x ⊩[M] A := by
  induction A generalizing x with
  | atom | falsum => rfl;
  | imp A B ihA ihB => exact imp_congr ihA ihB;
  | box A ih =>
    simp only [Formula.boxdotTranslate_box, forces_boxdot, forces_box, ih];
    constructor;
    · rintro ⟨h₁, h₂⟩ y Rxy;
      by_cases e : x = y;
      · exact e ▸ h₁;
      · exact h₂ y ⟨Rxy, e⟩;
    · intro h;
      exact ⟨h x (Std.Refl.refl x), fun y Rxy ↦ h y Rxy.1⟩;

end Kripke.Model

namespace Logic.Grz

universe u

variable {α : Type u} {A : Formula α}

theorem iff_boxdotTranslate_GL : 𝐆𝐫𝐳 ⊢ A ↔ 𝐆𝐋 ⊢ Aᵇ := by
  constructor;
  · intro h;
    apply GL.iff_valid_finite.mpr;
    intro _ _ M _ x;
    have hR : M.reflGen.irreflGen.Rel' = M.Rel' := by
      ext y z;
      change (y = z ∨ M.Rel y z) ∧ y ≠ z ↔ M.Rel y z;
      grind [Std.Irrefl.irrefl (r := M.Rel)];
    exact (forces_congr hR fun _ _ ↦ Iff.rfl).mp <|
      forces_irreflGen_boxdotTranslate.mpr (sound M.reflGen h x);
  · intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact forces_irreflGen_boxdotTranslate.mp (GL.iff_valid_finite.mp h M.irreflGen x);

theorem iff_boxdotTranslate_S : 𝐆𝐫𝐳 ⊢ A ↔ 𝐒 ⊢ Aᵇ :=
  iff_boxdotTranslate_GL.trans S.boxdotTranslate_iff_GL.symm

end Logic.Grz

instance {α : Type*} : Consistent (𝐆𝐫𝐳 : Logic α) :=
  .of_unprovable (φ := ⊥) fun h ↦ Logic.unprovable_bot (Logic.Grz.iff_boxdotTranslate_GL.mp h)

end FFL.ProvabilityLogic

end

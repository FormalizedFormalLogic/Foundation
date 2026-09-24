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

lemma forces_boxdotTranslate_axiomGrz [M.IsGL] {x : M.World} :
    x ⊩[M] ⊡(⊡(A 🡒 ⊡A) 🡒 A) 🡒 A := by
  induction x using WellFounded.induction (IsConverseWellFounded.cwf (rel := M.Rel)) with
  | _ x ih =>
    intro hx;
    obtain ⟨h₁, h₂⟩ := forces_boxdot.mp hx;
    have h₃ : ∀ z, x ≺ z → z ⊩[M] A := fun z Rxz ↦ ih z Rxz <|
      forces_boxdot.mpr ⟨h₂ z Rxz, fun w Rzw ↦ h₂ w (IsTrans.trans _ _ _ Rxz Rzw)⟩;
    apply h₁;
    apply forces_boxdot.mpr;
    and_intros;
    · exact fun hA ↦ forces_boxdot.mpr ⟨hA, h₃⟩;
    · exact fun y Rxy hy ↦ forces_boxdot.mpr ⟨hy, fun z Ryz ↦ h₃ z (IsTrans.trans _ _ _ Rxy Ryz)⟩;

end Kripke.Model

namespace Logic.Grz

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

omit [DecidableEq α] in
theorem iff_boxdotTranslate_GL : 𝐆𝐫𝐳 ⊢ A ↔ 𝐆𝐋 ⊢ Aᵇ := by
  constructor;
  · intro h;
    apply GL.iff_valid_finite.mpr;
    intro _ _ M _ x;
    induction h generalizing x with
    | axm hA =>
      rcases hA with ((⟨B, rfl⟩ | ⟨B, rfl⟩) | ⟨B, rfl⟩);
      · intro h;
        obtain ⟨-, h₂⟩ := forces_boxdot.mp h;
        exact forces_boxdot.mpr ⟨h, fun y Rxy ↦
          forces_boxdot.mpr ⟨h₂ y Rxy, fun z Ryz ↦ h₂ z (IsTrans.trans _ _ _ Rxy Ryz)⟩⟩;
      · exact fun h ↦ (forces_boxdot.mp h).1;
      · exact forces_boxdotTranslate_axiomGrz;
    | mdp _ _ ih₁ ih₂ => exact ih₁ x (ih₂ x);
    | nec _ ih => exact forces_boxdot.mpr ⟨ih x, fun y _ ↦ ih y⟩;
    | axiomK =>
      intro h₁ h₂;
      obtain ⟨h₁, h₁'⟩ := forces_boxdot.mp h₁;
      obtain ⟨h₂, h₂'⟩ := forces_boxdot.mp h₂;
      exact forces_boxdot.mpr ⟨h₁ h₂, fun y Rxy ↦ h₁' y Rxy (h₂' y Rxy)⟩;
    | _ => simp only [Axioms.Verum, Axioms.ImplyK, Axioms.ImplyS, Axioms.AndElim₁, Axioms.AndElim₂,
        Axioms.AndInst, Axioms.OrInst₁, Axioms.OrInst₂, Axioms.OrElim, Axioms.DNE,
        Formula.boxdotTranslate_imp, Formula.boxdotTranslate_and, Formula.boxdotTranslate_or,
        Formula.boxdotTranslate_neg, Formula.boxdotTranslate_top]; grind;
  · intro h;
    apply iff_valid_finite.mpr;
    intro _ _ M _ x;
    exact forces_irreflGen_boxdotTranslate.mp (GL.iff_valid_finite.mp h M.irreflGen x);

omit [DecidableEq α] in
theorem iff_boxdotTranslate_S : 𝐆𝐫𝐳 ⊢ A ↔ 𝐒 ⊢ Aᵇ :=
  iff_boxdotTranslate_GL.trans S.boxdotTranslate_iff_GL.symm

end Logic.Grz

end FFL.ProvabilityLogic

end

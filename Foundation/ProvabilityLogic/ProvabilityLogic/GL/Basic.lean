module

public import Foundation.ProvabilityLogic.Hilbert.GL.Basic
public import Foundation.ProvabilityLogic.ProvabilityLogic.SolovaySentences
public import Foundation.FirstOrder.Incompleteness.Löb

/-!
# Solovay's arithmetical completeness theorem

`GL` is the provability logic of every `Σ₁`-sound theory extending `𝗜𝚺₁` with a `Δ₁`
axiomatization, in particular of `𝗣𝗔`.

## References

- [Sol76]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Classical
open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Kripke Kripke.Model Kripke.Model.World

namespace GL

section

variable {α : Type*} {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T U : Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : Realization α L} {A : Formula α}

/-- The interpretation of a theorem of `GL` is provable in the base theory of the provability
predicate. -/
theorem arithmetical_soundness (h : ⊢ᴴ[GL] A) : T ⊢ A.interpret f 𝔅 := by
  obtain ⟨d⟩ := h;
  induction d with
  | nec _ ih => exact 𝔅.D1 (WeakerThan.pbl ih);
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | axiomK => exact 𝔅.D2;
  | axiom4 => exact 𝔅.D3;
  | axiomL => exact formalized_löb_theorem;
  | _ => dsimp [Formula.interpret]; cl_prover;

end

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}
         {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Solovay's arithmetical completeness theorem for theories of infinite height. -/
theorem arithmetical_completeness_of_height_eq_top (height : T.height = ⊤) :
    (∀ f : Realization α ℒₒᵣ, T ⊢ f T A) → ⊢ᴴ[GL] A := by
  contrapose!;
  intro hA;
  obtain ⟨κ, _, M, _, hA⟩ : ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
      M.root ⊮[M.toModel] A := by
    simpa using Hilbert.iff_root_forces.not.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists T M hA (by simp [height]);

/-- Solovay's arithmetical completeness theorem for theories of finite height. -/
theorem arithmetical_completeness_of_le_height {n : ℕ} (height : n ≤ T.height) :
    (∀ f : Realization α ℒₒᵣ, T ⊢ f T A) → ⊢ᴴ[GL] □^[n]⊥ 🡒 A := by
  contrapose!;
  intro hA;
  obtain ⟨κ, _, M, _, hA⟩ : ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
      M.root ⊮[M.toModel] □^[n]⊥ 🡒 A := by
    simpa using Hilbert.iff_root_forces.not.mp hA;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists T M h₂ <|
    lt_of_lt_of_le (Nat.cast_lt.mpr <| RootedModel.root_forces_boxItr_bot_iff.mp h₁) height;

/-- Solovay's arithmetical completeness theorem: `GL` proves exactly the modal formulas whose
standard interpretations are all provable in a `Σ₁`-sound theory `T`. -/
theorem arithmetical_completeness_iff [T.SoundOnHierarchy 𝚺 1] :
    ⊢ᴴ[GL] A ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ f T A :=
  ⟨fun h _ ↦ WeakerThan.pbl (arithmetical_soundness h),
    arithmetical_completeness_of_height_eq_top (Arithmetic.height_eq_top_of_sigma1_sound T)⟩

/-- `GL` is the provability logic of every `Σ₁`-sound theory. -/
theorem eq_provabilityLogic [T.SoundOnHierarchy 𝚺 1] :
    { A : Formula α | ⊢ᴴ[GL] A } = T.provabilityLogic := by
  ext A;
  exact arithmetical_completeness_iff;

/-- `GL` is the provability logic of `𝗣𝗔`. -/
theorem eq_provabilityLogic_peano : { A : Formula α | ⊢ᴴ[GL] A } = 𝗣𝗔.provabilityLogic :=
  eq_provabilityLogic

end GL

end FFL.ProvabilityLogic

end

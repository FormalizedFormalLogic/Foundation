module

public import Foundation.ProvabilityLogic.GL.Basic
public import Foundation.ProvabilityLogic.Arithmetic.SolovaySentences
public import Foundation.FirstOrder.Incompleteness.Löb

/-!
# Solovay's arithmetical completeness theorem

## References

- [Sol76]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Kripke Kripke.Model Kripke.Model.World

namespace Logic.GL

section

variable {α : Type*} {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T U : Theory L} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] {f : Realization α L} {A : Formula α}

/-- Arithmetical soundness of `GL`. -/
theorem arithmetical_soundness (h : 𝐆𝐋 ⊢ A) : T ⊢ A.interpret f 𝔅 := by
  induction h with
  | axm hA =>
    rcases hA with (⟨B, rfl⟩ | ⟨B, rfl⟩);
    · exact 𝔅.D3;
    · exact formalized_löb_theorem;
  | nec _ ih => exact 𝔅.D1 (WeakerThan.pbl ih);
  | mdp _ _ ih₁ ih₂ => exact ih₁ ⨀ ih₂;
  | axiomK => exact 𝔅.D2;
  | _ => dsimp [Formula.interpret]; cl_prover;

end

universe u

variable {α : Type u} {A : Formula α}
         {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Solovay's arithmetical completeness theorem for theories of infinite height. -/
theorem arithmetical_completeness_of_height_eq_top (height : T.height = ⊤) :
    (∀ f : Realization α ℒₒᵣ, T ⊢ f T A) → 𝐆𝐋 ⊢ A := by
  classical
  contrapose!;
  intro hA;
  obtain ⟨κ, _, M, _, hA⟩ :
      ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
        M.root ⊮[M.toModel] A := by
    simpa using iff_root_forces.not.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists T M hA (by simp [height]);

/-- Solovay's arithmetical completeness theorem for theories of finite height. -/
theorem arithmetical_completeness_of_le_height {n : ℕ} (height : n ≤ T.height) :
    (∀ f : Realization α ℒₒᵣ, T ⊢ f T A) → 𝐆𝐋 ⊢ □^[n]⊥ 🡒 A := by
  classical
  contrapose!;
  intro hA;
  obtain ⟨κ, _, M, _, hA⟩ :
      ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
        M.root ⊮[M.toModel] □^[n]⊥ 🡒 A := by
    simpa using iff_root_forces.not.mp hA;
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  exact unprovable_realization_exists T M h₂ <|
    lt_of_lt_of_le (Nat.cast_lt.mpr <| RootedModel.root_forces_boxItr_bot_iff.mp h₁) height;

/-- Solovay's arithmetical completeness theorem. -/
theorem arithmetical_completeness_iff [T.SoundOnHierarchy 𝚺 1] :
    𝐆𝐋 ⊢ A ↔ ∀ f : Realization α ℒₒᵣ, T ⊢ f T A :=
  ⟨fun h _ ↦ WeakerThan.pbl (arithmetical_soundness h),
    arithmetical_completeness_of_height_eq_top (Arithmetic.height_eq_top_of_sigma1_sound T)⟩

theorem eq_provabilityLogic [T.SoundOnHierarchy 𝚺 1] : 𝐆𝐋 over α = T.provabilityLogic := by
  ext A;
  exact arithmetical_completeness_iff;

theorem eq_provabilityLogic_peano : 𝐆𝐋 over α = 𝗣𝗔.provabilityLogic :=
  eq_provabilityLogic

end Logic.GL

end FFL.ProvabilityLogic

end

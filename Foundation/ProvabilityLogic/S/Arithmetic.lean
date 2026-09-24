module

public import Foundation.ProvabilityLogic.S.Basic
public import Foundation.ProvabilityLogic.GL.Arithmetic

/-!
# Solovay's arithmetical completeness theorem for `S`

## References

- [Sol76]
- [AB05]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Kripke Kripke.Model Kripke.Model.World

namespace Logic.S

section

variable {α : Type*} {T U : ArithmeticTheory} [Diagonalization T] [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL] [𝔅.SoundOn ℕ] [ℕ↓[ℒₒᵣ] ⊧* U] {A : Formula α}

/-- Arithmetical soundness of `S`.

- [Sol76]
-/
theorem arithmetical_soundness (h : 𝐒 ⊢ A) (f : Realization α ℒₒᵣ) :
    ℕ↓[ℒₒᵣ] ⊧ A.interpret f 𝔅 := by
  have : ℕ↓[ℒₒᵣ] ⊧* T := models_of_subtheory (T := T) (U := U) (M := ℕ) inferInstance;
  induction h generalizing f with
  | mem₁ h => exact models_of_provable inferInstance (GL.arithmetical_soundness h);
  | mem₂ h =>
    obtain ⟨B, rfl⟩ := h;
    simp only [Formula.interpret, Semantics.Imp.models_imply];
    exact fun h ↦ models_of_provable inferInstance (𝔅.sound_on h);
  | mdp _ _ ih₁ ih₂ =>
    simp only [Formula.interpret, Semantics.Imp.models_imply] at ih₁;
    exact ih₁ f (ih₂ f);
  | subst _ ih => simpa [Formula.interpret_subst] using ih _;

end

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}
         {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]

/-- Solovay's arithmetical completeness theorem for `S`: the formulas all of whose realizations are
true are exactly the theorems of `S`.

- [Sol76]
- [AB05, Theorem 3]
-/
theorem arithmetical_completeness (H : ∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ f T A) : 𝐒 ⊢ A := by
  have : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (T := 𝗜𝚺₁) (U := T) (M := ℕ) inferInstance;
  contrapose! H;
  obtain ⟨κ, _, M, _, hA⟩ :
      ∃ (κ : Type u) (_ : Nonempty κ) (M : RootedModel κ α) (_ : M.IsFiniteGL),
        M.root ⊮[M.toModel] A.rflSubfmls.conj 🡒 A := by
    simpa using GL.iff_root_forces.not.mp (iff_provable_GL.not.mp H);
  obtain ⟨h₁, h₂⟩ := not_forces_imp.mp hA;
  have : Fintype M.World := Fintype.ofFinite _;
  let S := standardSolovaySentences T M.extendRoot;
  use S.realization;
  have h₃ : ℕ↓[ℒₒᵣ] ⊧ S.σ none 🡒 ∼S.realization T A :=
    models_of_provable inferInstance <| (Provability.SolovaySentences.rfl_mainlemma
      (fun B hB ↦ forces_conj.mp h₁ _ (Finset.mem_image.mpr ⟨B, by simpa using hB, rfl⟩))
      Formula.mem_subfmls_self).2 h₂;
  have h₄ : ℕ↓[ℒₒᵣ] ⊧ S.σ none :=
    models_iff.mpr <| Arithmetic.Bootstrapping.SolovaySentences.val_solovay.mpr <|
      Arithmetic.Bootstrapping.SolovaySentences.solovay_root_sound (M := M.extendRoot);
  simp only [Semantics.Imp.models_imply, Semantics.Not.models_not] at h₃;
  exact h₃ h₄;

/-- - [AB05, Theorem 3] -/
theorem arithmetical_completeness_iff : 𝐒 ⊢ A ↔ ∀ f : Realization α ℒₒᵣ, ℕ↓[ℒₒᵣ] ⊧ f T A :=
  ⟨fun h f ↦ arithmetical_soundness h f, arithmetical_completeness⟩

theorem eq_provabilityLogicRelativeTo_TA : (𝐒 : Logic α) = T.provabilityLogicRelativeTo 𝗧𝗔 := by
  ext A;
  simpa [ArithmeticTheory.provabilityLogicRelativeTo, Arithmetic.TA.provable_iff, Logic.provable_iff_mem] using
    arithmetical_completeness_iff;

theorem eq_provabilityLogicRelativeTo_peano_TA :
    (𝐒 : Logic α) = 𝗣𝗔.provabilityLogicRelativeTo 𝗧𝗔 :=
  eq_provabilityLogicRelativeTo_TA

end Logic.S

end FFL.ProvabilityLogic

end

module

public import Foundation.ProvabilityLogic.A.Basic
public import Foundation.ProvabilityLogic.S.Arithmetic
public import Foundation.ProvabilityLogic.Trace

/-!
# Traces of provability logics

The provability logic of `T` relative to `U` contains `TBB n` for every `n` in its trace. Hence it
is `GLα` of its trace when the complement of its trace is infinite, and `GLβ⁻` of its trace when
it is not contained in `S`.

## References

- [AB05]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.ProvabilityAbstraction Kripke Kripke.Model Kripke.Model.World
open Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

/-! ### Closure properties -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {A : Formula α} {X : Logic α}

lemma provabilityLogic_of_GL (h : 𝐆𝐋 ⊢ A) : A ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun _ ↦ WeakerThan.pbl (Logic.GL.arithmetical_soundness h)

lemma sumQuasiNormal_subset_provabilityLogic (h : X ⊆ T.provabilityLogicRelativeTo U) :
    (𝐆𝐋 +ᴸ X) ⊆ (T.provabilityLogicRelativeTo U : Logic α) := by
  intro A hA;
  induction hA with
  | mem₁ hA => exact provabilityLogic_of_GL hA;
  | mem₂ hA => exact h hA;
  | mdp _ _ ih₁ ih₂ => exact provabilityLogic_mdp ih₁ ih₂;
  | subst _ ih => exact provabilityLogic_subst ih;

lemma provabilityLogic_conj [DecidableEq α] {Γ : FormulaFinset α}
    (h : ∀ B ∈ Γ, B ∈ (T.provabilityLogicRelativeTo U : Logic α)) :
    Γ.conj ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  sumQuasiNormal_subset_provabilityLogic (X := ↑Γ) (fun B hB ↦ h B hB) <|
    (FConj_iff_forall_provable (𝓢 := 𝐆𝐋 +ᴸ (Γ : Logic α))).mpr fun _ ↦ .mem₂

end

lemma LetterlessFormula.lift_mem_provabilityLogic {A : LetterlessFormula} (f : Realization α ℒₒᵣ)
    (h : U ⊢ f T A.lift) : A.lift ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  fun g ↦ by simpa only [standardInterpret, interpret_lift] using h

/-! ### Realizations from Solovay sentences -/

section

variable [𝗜𝚺₁ ⪯ T] {A : Formula α}

/-- - [AB05, Lemma 46] -/
lemma exists_realization_provable_imp_TBB {κ : Type*} [Nonempty κ] (M : RootedModel κ α)
    [Fintype M.World] [M.IsGL] (hA : M.root ⊮[M.toModel] A) :
    ∃ f : Realization α ℒₒᵣ, 𝗜𝚺₁ ⊢ f T (A 🡒 TBB M.height) := by
  sorry

/-- - [AB05, Lemma 49] -/
lemma exists_realization_provable_neg_of_not_S (hA : 𝐒 ⊬ A) :
    ∃ n, ∃ f : Realization α ℒₒᵣ,
      𝗜𝚺₁ ⊢ ∼f T (A ⋏ LetterlessFormula.lift (⩕ i ∈ Finset.range n, TBB i)) := by
  sorry

end

/-! ### Traces of provability logics -/

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U] {n : ℕ}

/-- - [AB05, Lemma 46, Corollary 47] -/
theorem TBB_mem_provabilityLogic_of_mem_trace
    (h : n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace) :
    TBB n ∈ (T.provabilityLogicRelativeTo U : Logic α) := by
  sorry

/-- - [AB05, Corollary 47] -/
theorem mem_trace_provabilityLogic_iff :
    n ∈ (T.provabilityLogicRelativeTo U : Logic α).trace ↔
      TBB n ∈ (T.provabilityLogicRelativeTo U : Logic α) :=
  sorry

/-- - [AB05, Corollary 48] -/
theorem provabilityLogic_eq_GLAlpha
    (h : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Infinite) :
    (T.provabilityLogicRelativeTo U : Logic α) =
      𝐆𝐋α (T.provabilityLogicRelativeTo U : Logic α).trace :=
  sorry

lemma exists_neg_conj_TBB_mem_provabilityLogic
    (h : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    ∃ m, LetterlessFormula.lift (∼⩕ i ∈ Finset.range m, TBB i) ∈
      (T.provabilityLogicRelativeTo U : Logic α) := by
  sorry

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_trace_compl_finite
    (h : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite := by
  sorry

/-- - [AB05, Lemma 49] -/
theorem betaMinus_mem_provabilityLogic (h : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (betaMinus _ (provabilityLogic_trace_compl_finite h)).lift ∈
      (T.provabilityLogicRelativeTo U : Logic α) := by
  sorry

/-- - [AB05, Lemma 49] -/
theorem provabilityLogic_eq_GLBetaMinus (h : ¬(T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo U : Logic α) =
      𝐆𝐋β⁻ (T.provabilityLogicRelativeTo U : Logic α).trace
        (provabilityLogic_trace_compl_finite h) :=
  sorry

/-- - [AB05, Corollary 50] -/
theorem A_subset_provabilityLogic (h : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) :
    𝐀 ⊆ (T.provabilityLogicRelativeTo U : Logic α) :=
  sorry

end

end FFL.ProvabilityLogic

end
